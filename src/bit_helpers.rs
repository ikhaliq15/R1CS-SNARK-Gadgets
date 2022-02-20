use curve25519_dalek::scalar::Scalar;

/*  return the value of the I-th bit of BITS, where
    the LSB is i=0 and the MSB is i=255. assume BITS
    is stored in little endian format. */
pub fn get_bit(bits: [u8; 32], i: usize) -> u8 {
    (bits[i / 8] >> (i % 8)) & 1
}

/*  set the value of the I-th bit of BITS to B, where
    the LSB is i=0 and the MSB is i=255. assume BITS
    is stored in little endian format. */
pub fn set_bit(bits: &mut [u8; 32], i: usize, b: u8) {
    bits[i / 8] = (bits[i / 8] & !(1u8 << (i % 8))) | ((b & 1) << (i % 8));
}

/*  return the sum of the N most significant bits from BITS.
    assume BITS is stored in little endian format. */
pub fn sum_last_n_bits(bits: [u8; 32], n: usize) -> u8 {
    ((256 - n)..256).map(|i| get_bit(bits, i)).sum()
}

/*  return 2^N as a scalar. assumes 2^N will fit in a scalar. */
pub fn get_pow_2(n: usize) -> Scalar {
    let mut bits: [u8; 32] = [0u8; 32];
    set_bit(&mut bits, n, 1);
    Scalar::from_bits(bits)
}

#[cfg(test)]
mod bit_helper_tests {
    use curve25519_dalek::scalar::Scalar;
    use crate::bit_helpers::{get_bit, set_bit, sum_last_n_bits};
    use crate::get_pow_2;

    #[test]
    fn get_bit_test() {
        let zeroes: [u8; 32] = [0u8; 32];
        for i in 0..256 {
            assert_eq!(get_bit(zeroes, i), 0, "testing bit {}", i);
        }

        let bits: [u8; 32] = [
            0xA3, 0x03, 0x10, 0x5B, 0x72, 0x03, 0x12, 0xDE,
            0x26, 0x11, 0x17, 0x92, 0x82, 0xA6, 0x02, 0xD7,
            0xA3, 0x00, 0x10, 0x5B, 0x12, 0x32, 0x28, 0x27,
            0x5F, 0x21, 0x20, 0xE3, 0xAA, 0xB5, 0x86, 0xB9,
        ];

        let expected_bits: [u8; 256] = [
            1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0,
            0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0,
            0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1,
            0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0,
            1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1,
            0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1,
            0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1,
            1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0,
            0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0,
            0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0,
            1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0,
            0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1,
            0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1,
            0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1,
        ];

        for i in 0..256 {
            assert_eq!(get_bit(bits, i), expected_bits[i], "testing bit {}", i);
        }
    }

    #[test]
    fn get_set_test() {
        let new_bits: [u8; 256] = [
            1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0,
            0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0,
            0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1,
            0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0,
            1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1,
            0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1,
            0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1,
            1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0,
            0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0,
            0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0,
            1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0,
            0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1,
            0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1,
            0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1,
        ];

        let expected_bytes: [u8; 32] = [
            0xA3, 0x03, 0x10, 0x5B, 0x72, 0x03, 0x12, 0xDE,
            0x26, 0x11, 0x17, 0x92, 0x82, 0xA6, 0x02, 0xD7,
            0xA3, 0x00, 0x10, 0x5B, 0x12, 0x32, 0x28, 0x27,
            0x5F, 0x21, 0x20, 0xE3, 0xAA, 0xB5, 0x86, 0xB9,
        ];

        let mut bits: [u8; 32] = [0u8; 32];
        for i in 0..256 {
            assert_eq!(get_bit(bits, i), 0, "testing bit {}", i);
        }

        for i in 0..256 {
            set_bit(&mut bits, i, new_bits[i]);
            assert_eq!(get_bit(bits, i), new_bits[i], "testing bit {}", i);
        }

        for i in 0..32 {
            assert_eq!(bits[i], expected_bytes[i], "testing byte {}", i);
        }
    }

    #[test]
    fn sum_last_n_bits_test() {
        let bits: [u8; 32] = [
            0xA3, 0x03, 0x10, 0x5B, 0x72, 0x03, 0x12, 0xDE,
            0x26, 0x11, 0x17, 0x92, 0x82, 0xA6, 0x02, 0xD7,
            0xA3, 0x00, 0x10, 0x5B, 0x12, 0x32, 0x28, 0x27,
            0x5F, 0x21, 0x20, 0xE3, 0xAA, 0xB5, 0x86, 0xB9,
        ];

        let expected_sums: [u8; 256] = [
              0,   1,   1,   2,   3,   4,   4,   4,   5,   6,   6,   6,   6,   6,   7,   8,
              8,   9,   9,  10,  11,  11,  12,  12,  13,  14,  14,  15,  15,  16,  16,  17,
             17,  18,  19,  20,  20,  20,  20,  21,  22,  22,  22,  23,  23,  23,  23,  23,
             23,  23,  23,  24,  24,  24,  24,  24,  25,  25,  26,  26,  27,  28,  29,  30,
             31,  31,  31,  32,  32,  32,  33,  34,  35,  35,  35,  36,  36,  37,  37,  37,
             37,  37,  37,  38,  39,  39,  39,  40,  40,  40,  40,  40,  41,  41,  41,  42,
             42,  42,  43,  43,  44,  45,  45,  46,  47,  47,  47,  47,  48,  48,  48,  48,
             48,  48,  48,  48,  48,  48,  48,  48,  48,  49,  49,  50,  50,  50,  50,  51,
             52,  53,  54,  54,  55,  55,  56,  57,  58,  58,  58,  58,  58,  58,  58,  59,
             59,  60,  60,  61,  61,  61,  62,  63,  63,  64,  64,  64,  64,  64,  64,  65,
             65,  66,  66,  66,  67,  67,  67,  68,  68,  68,  68,  68,  69,  69,  70,  71,
             72,  72,  72,  72,  73,  73,  73,  73,  74,  74,  74,  75,  75,  75,  76,  77,
             77,  78,  79,  79,  80,  81,  82,  83,  83,  83,  83,  83,  84,  84,  84,  85,
             85,  85,  85,  85,  85,  85,  85,  86,  87,  87,  88,  89,  90,  90,  90,  91,
             91,  91,  92,  92,  93,  94,  94,  95,  96,  96,  96,  96,  97,  97,  97,  97,
             97,  97,  97,  97,  97,  97,  97,  98,  99, 100, 100, 101, 101, 101, 101, 102,
        ];

        for i in 0..256 {
            assert_eq!(sum_last_n_bits(bits, i), expected_sums[i], "testing sum of last {} bits", i);
        }
    }

    #[test]
    fn get_pow_2_test() {
        let mut power: Scalar = Scalar::one();
        let two: Scalar = Scalar::from(2u32);
        for i in 0..253 {
            assert!(get_pow_2(i).eq(&power));
            power = power * two;
        }
    }
}