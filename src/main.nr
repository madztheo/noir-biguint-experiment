// Actual size in bits of the number
global L: u64 = 1024;
// Number of bits per limb
// We set it to 120-bit limbs.
global D: u64 = 120;
// Take the ceiling of L/D
// 1024 / 120 = 9 limbs
global N: u64 = (L + D - 1) / D;
// 2^128 - 1
global P: [Field; N] = [0xffffffffffffffffffffffffffffff, 0xff, 0, 0, 0, 0, 0, 0, 0];
// 2^120 to constrain the limb size
global LIMB_MODULO: Field = 1329227995784915872903807060280344576;

fn compute_product(a: [Field; N], b: [Field; N]) -> [Field; N * 2 - 1] {
    let mut output = [0; N * 2 - 1];
    for i in 0..(N * 2 - 1) {
        for j in 0..(i+1) {
            if (j < N) & (i - j < N) {
                output[i] += a[j] * b[i - j];
            }
        }
    }

    output
}

fn main() {
    let a: [Field; N] = [0xffffffffffffffffffffffffffffff, 0, 0, 0, 0, 0, 0, 0, 0];
    let b: [Field; N] = [2, 0, 0, 0, 0, 0, 0, 0, 0];
    let c = compute_product(a, b);
    println(c);
}