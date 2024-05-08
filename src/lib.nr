/*
* The idea is to start implementing the different parts of the specs using directly 
* an array of numbers rather relying on a Struct at the moment. Once we have more solid
* functions to handle the most important operations, we can start to refactor the code
* to use a Struct to represent the BigUint.
*/

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
global LIMB_MODULUS: Field = 1329227995784915872903807060280344576;

fn biguint_less_than<SIZE>(x: [Field; SIZE], y: [Field; SIZE]) -> bool {
    // TODO: Implement the comparison function

    false
}

unconstrained fn biguint_divide<SIZE>(x: [Field; SIZE], y: [Field; SIZE]) -> ([Field; SIZE], [Field; SIZE]){
    if biguint_less_than(x, y) {
        ([0; SIZE], x)
    }

    // Quotient
    let mut q = [0; SIZE];
    // Remainder
    let mut r = x;

    // TODO: Implement a long division algorithm to x and y get the quotient and the remainder
    // c.f. https://people.eecs.berkeley.edu/~fateman/282/F%20Wright%20notes/week4.pdf
    // c.f. https://github.com/madztheo/noir-large-integer/blob/57dc1b45ff5cb90869602ef201e99adca1d5339b/crates/large-integer-64/src/lib.nr#L295

    (q, r)
}

#[test]
fn test_biguint_less_than() {
    let a: [Field; N] = [2, 0, 0, 0, 0, 0, 0, 0, 0];
    let b: [Field; N] = [3, 0, 0, 0, 0, 0, 0, 0, 0];

    // TODO: Make the test pass
    assert(biguint_less_than(a, b));
}

#[test]
fn test_biguint_divide() {
    let a: [Field; N] = [0xffffffffffffffffffffffffffffff, 0, 0, 0, 0, 0, 0, 0, 0];
    let b: [Field; N] = [2, 0, 0, 0, 0, 0, 0, 0, 0];

    let (q, r) = biguint_divide(a, b);
    println(q);
    println(r);

    // TODO: Test that the result of the division is correct
}