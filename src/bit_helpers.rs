pub fn sum_last_n_bits(
    bits: [u8; 32],
    n: usize
) -> u8 {
    let mut sum: u8 = 0;
    let mut i: usize = 0;
    for block in bits {
        for j in 0..8 {
            if i + j >= 256 - n {
                sum += (block >> j) & 1;
            }
        }
        i += 8;
    }
    sum
}