#![no_std]
use ethnum::u256;

pub struct Bn254;

impl Bn254 {
    /// BN254 scalar field modulus r (order of G1/G2).
    pub const FR_MODULUS: ethnum::u256 = ethnum::u256::from_words(
        0x30644e72e131a029b85045b68181585d_u128, // high 128 bits
        0x2833e84879b9709143e1f593f0000001_u128, // low 128 bits
    );

    /// BN254 base field modulus p (coordinate field of the curve).
    pub const FQ_MODULUS: ethnum::u256 = ethnum::u256::from_words(
        0x30644e72e131a029b85045b68181585d_u128,
        0x97816a916871ca8d3c208c16d87cfd47_u128,
    );

    /// (r - 1) / 2 — Legendre exponent for the scalar field Fr.
    /// Pre-computed to avoid runtime division; used by `legendre_fr`.
    pub const LEGENDRE_EXP_FR: ethnum::u256 = ethnum::u256::from_words(
        0x183227397098d014dc2822db40c0ac2e_u128,
        0x9419f4243cdcb848a1f0fac9f8000000_u128,
    );

    /// (p - 1) / 2 — Legendre exponent for the base field Fq.
    /// Pre-computed to avoid runtime division; used by `legendre_fq`.
    pub const LEGENDRE_EXP_FQ: ethnum::u256 = ethnum::u256::from_words(
        0x183227397098d014dc2822db40c0ac2e_u128,
        0xcbc0b548b438e5469e10460b6c3e7ea3_u128,
    );

    // ── Private generic helpers ───────────────────────────────────────────────

    #[inline(always)]
    fn add_mod(a: u256, b: u256, modulus: u256) -> u256 {
        let (sum, overflow) = a.overflowing_add(b);
        if overflow || sum >= modulus {
            sum.wrapping_sub(modulus)
        } else {
            sum
        }
    }

    /// Modular Multiplication: (a * b) % modulus
    /// Implements manual 512-bit long multiplication to bypass library limitations.
    #[inline(always)]
    fn mul_mod(a: u256, b: u256, modulus: u256) -> u256 {
        if a == 0 || b == 0 {
            return u256::from(0u8);
        }

        // Split a and b into 128-bit halves
        let a_low = u256::from(a.as_u128());
        let a_high = a >> 128;
        let b_low = u256::from(b.as_u128());
        let b_high = b >> 128;

        // Schoolbook multiplication (a_hi*2^128 + a_lo) * (b_hi*2^128 + b_lo)
        // This yields 4 partial products
        let p0 = a_low * b_low;
        let p1 = a_low * b_high;
        let p2 = a_high * b_low;
        let p3 = a_high * b_high;

        // Perform modular reduction on each partial product stage
        // to keep everything within 256-bit bounds.
        let mut res = p0;
        while res >= modulus {
            res -= modulus;
        }

        // Handle p1 and p2 (shifted by 128 bits)
        let mut p1_red = p1;
        while p1_red >= modulus {
            p1_red -= modulus;
        }
        let mut p2_red = p2;
        while p2_red >= modulus {
            p2_red -= modulus;
        }
        
        let mut p1_p2 = Self::add_mod(p1_red, p2_red, modulus);
        for _ in 0..128 {
            p1_p2 = Self::add_mod(p1_p2, p1_p2, modulus); // Modular doubling
        }
        res = Self::add_mod(res, p1_p2, modulus);

        // Handle p3 (shifted by 256 bits)
        let mut p3_red = p3;
        while p3_red >= modulus {
            p3_red -= modulus;
        }
        for _ in 0..256 {
            p3_red = Self::add_mod(p3_red, p3_red, modulus); // Modular doubling
        }
        res = Self::add_mod(res, p3_red, modulus);

        res
    }

    #[inline(always)]
    fn pow_mod(mut base: u256, mut exp: u256, modulus: u256) -> u256 {
        let mut res = u256::from(1u8);
        while exp > 0 {
            if exp % 2 == 1 {
                res = Self::mul_mod(res, base, modulus);
            }
            base = Self::mul_mod(base, base, modulus);
            exp /= 2;
        }
        res
    }

    // ── Public Fr (scalar field) arithmetic ──────────────────────────────────

    pub fn is_valid_scalar(val: u256) -> bool {
        val < Self::FR_MODULUS
    }

    pub fn add(a: u256, b: u256) -> u256 {
        Self::add_mod(a, b, Self::FR_MODULUS)
    }

    pub fn mul(a: u256, b: u256) -> u256 {
        Self::mul_mod(a, b, Self::FR_MODULUS)
    }

    pub fn pow(base: u256, exp: u256) -> u256 {
        Self::pow_mod(base, exp, Self::FR_MODULUS)
    }

    pub fn invert(a: u256) -> u256 {
        if a == 0 {
            return u256::from(0u8);
        }
        let exponent = Self::FR_MODULUS - u256::from(2u8);
        Self::pow(a, exponent)
    }

    pub fn is_valid_g1(x: u256, y: u256) -> bool {
        if x == 0 && y == 0 {
            return false;
        }
        if x >= Self::FQ_MODULUS || y >= Self::FQ_MODULUS {
            return false;
        }

        let y_sq = Self::mul_mod(y, y, Self::FQ_MODULUS);
        let x_sq = Self::mul_mod(x, x, Self::FQ_MODULUS);
        let x_cb = Self::mul_mod(x_sq, x, Self::FQ_MODULUS);
        let rhs = Self::add_mod(x_cb, u256::from(3u8), Self::FQ_MODULUS);

        y_sq == rhs
    }

    // ── Legendre symbol / quadratic residue ──────────────────────────────────

    /// Legendre symbol (a | r) for the BN254 scalar field Fr.
    ///
    /// Computes `a^((r-1)/2) mod r` using the pre-computed [`LEGENDRE_EXP_FR`]
    /// constant — no runtime division.
    ///
    /// Returns:
    /// -  `0`  if `a == 0`
    /// -  `1`  if `a` is a non-zero quadratic residue mod r
    /// - `-1`  if `a` is a quadratic non-residue mod r
    pub fn legendre_fr(a: u256) -> i8 {
        if a == 0 {
            return 0;
        }
        let result = Self::pow_mod(a, Self::LEGENDRE_EXP_FR, Self::FR_MODULUS);
        if result == u256::from(1u8) {
            1
        } else {
            -1 // result == FR_MODULUS - 1, i.e. -1 in the field
        }
    }

    /// Legendre symbol (a | p) for the BN254 base field Fq.
    ///
    /// Computes `a^((p-1)/2) mod p` using the pre-computed [`LEGENDRE_EXP_FQ`]
    /// constant — no runtime division.
    ///
    /// Returns:
    /// -  `0`  if `a == 0`
    /// -  `1`  if `a` is a non-zero quadratic residue mod p
    /// - `-1`  if `a` is a quadratic non-residue mod p
    pub fn legendre_fq(a: u256) -> i8 {
        if a == 0 {
            return 0;
        }
        let result = Self::pow_mod(a, Self::LEGENDRE_EXP_FQ, Self::FQ_MODULUS);
        if result == u256::from(1u8) {
            1
        } else {
            -1 // result == FQ_MODULUS - 1, i.e. -1 in the field
        }
    }

    /// Returns `true` if `a` is a quadratic residue in the scalar field Fr.
    ///
    /// Convenience wrapper around [`legendre_fr`]. Zero is **not** considered
    /// a quadratic residue by this function.
    pub fn is_quadratic_residue_fr(a: u256) -> bool {
        Self::legendre_fr(a) == 1
    }

    /// Returns `true` if `a` is a quadratic residue in the base field Fq.
    ///
    /// Convenience wrapper around [`legendre_fq`]. Zero is **not** considered
    /// a quadratic residue by this function.
    pub fn is_quadratic_residue_fq(a: u256) -> bool {
        Self::legendre_fq(a) == 1
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ── legendre_fr ───────────────────────────────────────────────────────────

    #[test]
    fn legendre_fr_zero_returns_0() {
        assert_eq!(Bn254::legendre_fr(u256::from(0u8)), 0);
    }

    #[test]
    fn legendre_fr_one_is_residue() {
        // 1 = 1^2
        assert_eq!(Bn254::legendre_fr(u256::from(1u8)), 1);
    }

    #[test]
    fn legendre_fr_perfect_square_is_residue() {
        // 4 = 2^2
        assert_eq!(Bn254::legendre_fr(u256::from(4u8)), 1);
    }

    #[test]
    fn legendre_fr_any_square_is_residue() {
        // Euler's criterion: (x^2)^((r-1)/2) = x^(r-1) = 1 (Fermat) for x != 0
        let x = u256::from(17u8);
        let x_sq = Bn254::mul(x, x);
        assert_eq!(Bn254::legendre_fr(x_sq), 1);
    }

    #[test]
    fn legendre_fr_five_is_non_residue() {
        // Proved via QR: (5/r) = (r mod 5 / 5) = (2/5) = -1
        assert_eq!(Bn254::legendre_fr(u256::from(5u8)), -1);
    }

    #[test]
    fn legendre_fr_neg_one_is_residue() {
        // r ≡ 1 (mod 4), so -1 IS a quadratic residue in Fr!
        let neg_one = Bn254::FR_MODULUS - u256::from(1u8);
        assert_eq!(Bn254::legendre_fr(neg_one), 1);
    }

    // ── legendre_fq ───────────────────────────────────────────────────────────

    #[test]
    fn legendre_fq_zero_returns_0() {
        assert_eq!(Bn254::legendre_fq(u256::from(0u8)), 0);
    }

    #[test]
    fn legendre_fq_one_is_residue() {
        assert_eq!(Bn254::legendre_fq(u256::from(1u8)), 1);
    }

    #[test]
    fn legendre_fq_perfect_square_is_residue() {
        assert_eq!(Bn254::legendre_fq(u256::from(4u8)), 1);
        assert_eq!(Bn254::legendre_fq(u256::from(9u8)), 1);
    }


    #[test]
    fn legendre_fq_five_is_non_residue() {
        // Proved via QR: (5/p) = (p mod 5 / 5) = (3/5) = -1
        assert_eq!(Bn254::legendre_fq(u256::from(5u8)), -1);
    }

    // ── is_quadratic_residue_fr ───────────────────────────────────────────────

    #[test]
    fn is_qr_fr_square_is_true() {
        assert!(Bn254::is_quadratic_residue_fr(u256::from(4u8)));
    }

    #[test]
    fn is_qr_fr_non_residue_is_false() {
        assert!(!Bn254::is_quadratic_residue_fr(u256::from(5u8)));
    }

    #[test]
    fn is_qr_fr_zero_is_false() {
        assert!(!Bn254::is_quadratic_residue_fr(u256::from(0u8)));
    }

    // ── is_quadratic_residue_fq ───────────────────────────────────────────────

    #[test]
    fn is_qr_fq_square_is_true() {
        assert!(Bn254::is_quadratic_residue_fq(u256::from(4u8)));
    }

    #[test]
    fn is_qr_fq_non_residue_is_false() {
        assert!(!Bn254::is_quadratic_residue_fq(u256::from(5u8)));
    }

    #[test]
    fn is_qr_fq_zero_is_false() {
        assert!(!Bn254::is_quadratic_residue_fq(u256::from(0u8)));
    }

    // ── Constant sanity checks ────────────────────────────────────────────────

    #[test]
    fn legendre_exp_fr_is_half_of_r_minus_one() {
        // LEGENDRE_EXP_FR * 2 must equal FR_MODULUS - 1
        let doubled = Bn254::LEGENDRE_EXP_FR
            .checked_add(Bn254::LEGENDRE_EXP_FR)
            .unwrap();
        assert_eq!(doubled, Bn254::FR_MODULUS - u256::from(1u8));
    }

    #[test]
    fn legendre_exp_fq_is_half_of_p_minus_one() {
        // LEGENDRE_EXP_FQ * 2 must equal FQ_MODULUS - 1
        let doubled = Bn254::LEGENDRE_EXP_FQ
            .checked_add(Bn254::LEGENDRE_EXP_FQ)
            .unwrap();
        assert_eq!(doubled, Bn254::FQ_MODULUS - u256::from(1u8));
    }
}
