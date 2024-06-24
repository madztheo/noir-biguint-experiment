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
global B: Field = 1329227995784915872903807060280344576;
// BN254 modulus - 1 => Max value of a Field
global BN254_MINUS_1 = 21888242871839275222246405745257275088548364400416034343698204186575808495616;

trait FieldUtils {
    fn gte(self, other: Self) -> bool;
    fn lte(self, other: Self) -> bool;
    fn gt(self, other: Self) -> bool;
}

impl FieldUtils for Field {
    fn gte(self, other: Self) -> bool {
        (other.lt(self)) | (self == other)
    }

    fn lte(self, other: Self) -> bool {
        (self.lt(other)) | (self == other)
    }

    fn gt(self, other: Self) -> bool {
        other.lt(self)
    }

}

fn to_bits<SIZE>(val: [Field; SIZE]) -> [u1; L] {
    let mut res = [0 as u1; L];

    for i in 0..N {
        let limb_bits = val[i].to_le_bits(D as u32);
        for j in 0..D {
            let idx = i * D + j;
            res[idx] = limb_bits[j];
        }
    }

    res
}

fn nbits<SIZE>(val: [Field; SIZE]) -> u64 {
    let bits = to_bits(val);
    let mut res = 0;
    let mut done = false;
    for i in 0..L {
        if !done {
            if bits[L - i - 1] != 0 {
                res = (L - i - 1) as u64 + 1;
                done = true;
            }
        }
    }

    if res == 0 {
        res = 1;
    }

    res
}

fn nlimbs<SIZE>(val: [Field; SIZE]) -> u64 {
    let mut res = 0;
    let mut done = false;
    for i in 0..SIZE {
        if !done {
            if val[SIZE - i - 1] != 0 {
                res = (SIZE - i - 1) as u64 + 1;
                done = true;
            }
        }
    }

    if res == 0 {
        res = 1;
    }

    res
}

/**
* Compare two big integers x and y and return:
* 0 if x == y
* 1 if x < y
* 2 if x > y
*/
fn compare<SIZE>(x: [Field; SIZE], y: [Field; SIZE]) -> u8 {
    let mut r = 0;
    let mut stop = false;
    for i in 0..SIZE {
        let real_index: i32 = SIZE - i - 1;
        if (x[real_index] != y[real_index]) & (stop == false) {
            if (x[real_index].lt(y[real_index])) {
                r = 1;
            } else {
                r = 2;
            }
            stop = true;
        }
    }

    r
}

fn equal<SIZE>(x: [Field; SIZE], y: [Field; SIZE]) -> bool {
    let res = compare(x, y);
    res == 0
}

fn less_than<SIZE>(x: [Field; SIZE], y: [Field; SIZE]) -> bool {
    let res = compare(x, y);
    // 1 means that x is less than y
    res == 1
}

fn less_than_equal<SIZE>(x: [Field; SIZE], y: [Field; SIZE]) -> bool {
    // We repeat ourselves a bit here and don't call equal and less_than
    // so that we can call compare only once
    let r = compare(x, y);
    (r == 0) | (r == 1)
}

fn greater_than<SIZE>(x: [Field; SIZE], y: [Field; SIZE]) -> bool {
    let r = compare(x, y);
    // 2 means that x is greater than y
    r == 2
}

fn greater_than_equal<SIZE>(x: [Field; SIZE], y: [Field; SIZE]) -> bool {
    // We repeat ourselves a bit here and don't call equal and greater_than
    // so that we can call compare only once
    let r = compare(x, y);
    (r == 0) | (r == 2)
}

// c.f. https://people.eecs.berkeley.edu/~fateman/282/F%20Wright%20notes/week4.pdf - Algorithm in 2.1 
fn add<SIZE>(x: [Field; SIZE], y: [Field; SIZE]) -> [Field; SIZE] {
    let mut r: Field = 0;
    let m = nlimbs(x);
    let k = m - 1;
    let mut c = [0 as Field; SIZE];

    for i in 0..SIZE {
        let s = x[i] + y[i] + r;
        if s.lt(B) {
            c[i] = s;
            r = 0;
        } else {
            c[i] = s - B as Field;
            r = 1;
        }
    }

    if r == 1 {
        c[m] = 1;
    }

    c
}

// c.f. https://people.eecs.berkeley.edu/~fateman/282/F%20Wright%20notes/week4.pdf - Algorithm in 2.2
fn sub<SIZE>(x: [Field; SIZE], y: [Field; SIZE]) -> [Field; SIZE] {
    assert(less_than_equal(y, x), "Subtraction underflow");

    let mut r: Field = 0;
    let mut s: Field = 0;
    let mut c = [0 as Field; SIZE];

    for i in 0..SIZE {
        s = x[i] - y[i] - r;
        // We check that x[i] >= y[i] + r
        // i.e. s >= 0
        if x[i].gte(y[i] + r) {
            c[i] = s;
            r = 0;
        } else {
            c[i] = s + B as Field;
            r = 1;
        }
    }

    c
}

// TODO: Improve the performance of this integer division between two Field
unconstrained fn unconstrained_integer_div(x: Field, y: Field) -> (Field, Field) {
    if y == 0 {
        (0, 0)
    } else if x.lt(y) {
        (0, x)
    } else if x == y {
        (1, 0)
    } else {
        let (q,r) = integer_div(x, y * 2);
        let q_mul_2 = q * 2;
        if r.lt(y) {
            (q_mul_2, r)
        } else {
            (q_mul_2 + 1, r - y)
        }
    }
}

fn integer_div(x: Field, y: Field) -> (Field, Field) {
    let (q, r) = unconstrained_integer_div(x, y);
    let x_prime = y * q + r;
    assert(x_prime == x, "Division error");
    assert(r.lt(y), "Remainder error");
    (q, r)
}

fn scalar_mul<SIZE>(x: [Field; SIZE], y: Field) -> [Field; SIZE] {
    let mut c: [Field; SIZE] = [0; SIZE];
    let m = nlimbs(x);
    let mut r: Field = 0;

    for i in 0..SIZE {
        let s = x[i] * y + r;
        let (q, _r) = integer_div(s, B);
        c[i] = _r;
        r = q;
    }

    c
}

// c.f. https://people.eecs.berkeley.edu/~fateman/282/F%20Wright%20notes/week4.pdf - Second algorithm in 3
fn normalized_mul<SIZE>(x: [Field; SIZE], y: [Field; SIZE]) -> [Field; SIZE] {
    let mut c: [Field; 2 * N] = [0; 2 * N];
    let m = nlimbs(x);
    let n = nlimbs(y);
    let k = m + n;
    let mut r: Field = 0;

    for i in 0..SIZE {
        for j in 0..SIZE {
            let s: Field = x[j] * y[i] + c[i + j] + r;
            let (q, _r) = integer_div(s, B);
            c[i + j] = _r;
            r = q;
        }
        c[i+m] += r;
    }

    let mut normalized_c = [0; SIZE];

    for i in 0..SIZE {
        normalized_c[i] = c[i];
    }

    normalized_c
}

// c.f. https://people.eecs.berkeley.edu/~fateman/282/F%20Wright%20notes/week4.pdf - Algorithm in 4.1
fn find_quotient_limb<SIZE>(x: [Field; SIZE], y: [Field; SIZE], d: Field) -> Field {
    let mut n = nlimbs(y);

    let scaled_x = scalar_mul(x, d);
    let scaled_y = scalar_mul(y, d);

    // Q_hat = min(B - 1, floor((x[0]*B + x[1]) / y[0]))
    // With index 0 and 1 assuming that the limbs are 
    // from the most significant to the least significant
    // Which is the opposite of the order used here
    let dividend = scaled_x[n] * B + scaled_x[n - 1];
    let divisor = scaled_y[n - 1];

    // Put the value of Q_hat into Q
    let (mut q, _) = integer_div(dividend, divisor);

    if q.gt(B - 1) {
        q = B - 1;
    }

    let mut product = scalar_mul(scaled_y, q);

    // There are only 3 iterations possible so we can rely on just
    // if statements

    // This is equivalent to checking that the remainder is negative
    // so that we don't have to deal with negative numbers
    if greater_than(product, scaled_x) {
        product = sub(product, scaled_y);
        if greater_than(product, scaled_x) {
            q = q - 2;
        } else {
            q = q - 1;
        }
    }

    q
}

// c.f. https://people.eecs.berkeley.edu/~fateman/282/F%20Wright%20notes/week4.pdf - Algorithm in 4
unconstrained fn divide<SIZE>(x: [Field; SIZE], y: [Field; SIZE]) -> ([Field; SIZE], [Field; SIZE]) {
    if less_than(x, y) {
        ([0; SIZE], x)
    }

    // Quotient
    let mut q = [0; SIZE];

    // The actual length of x
    let m = nlimbs(x);
    // The actual length of y
    let n = nlimbs(y);
    let k = m - n + 1;

    // Remainder
    let mut r = [0; N + 1];

    let mut resized_x = [0; N + 1];
    for i in 0..m {
        resized_x[i] = x[i];
    }

    // Resize y to match the size of r
    // so we can do operations between them
    let mut resized_y = [0; N + 1];
    for i in 0..n {
        resized_y[i] = y[i];
    }

    // d is the scaling factor use to scale x and y
    // so that the most significant limb of y is at least B/2
    // which is a necessary condition for the following algorithm
    // to work
    let (d, _) = integer_div(B, y[n - 1] + 1);

    // Initiate the remainder to the first n limbs of x
    for i in 0..n {
        r[i] = x[m - i - 1];
    }
    for i in 0..n {
        r[i] = r[n - i - 1];
    }

    for i in 0..k {
        // Compared to other operations, we need to reverse the order of the index
        // as we are going from the most significant limb to the least significant limb
        let real_index = k - i - 1;
        q[real_index] = find_quotient_limb(r, resized_y, d);
        r = sub(r, scalar_mul(resized_y, q[real_index]));
        if i != k - 1 {
            let mut shifted_r = [0; N + 1];
            for j in 0..n {
                shifted_r[j + 1] = r[j];
            }
            r = shifted_r;
            // Take down the following limb of x into the dividend
            r[0] = resized_x[m - n - i - 1];
        }
    }

    // The following two asserts should be used to check that the division
    // is correct in constrained code
    //assert(x == add(normalized_mul(q, y), r), "Division error");
    //assert(less_than_equal(r, y), "Remainder error");

    let mut final_r = [0; SIZE];
    for i in 0..SIZE {
        final_r[i] = r[i];
    }

    (q, final_r)
}

#[test]
fn test_field_lt() {
    let a: Field = 2;
    let b: Field = 3;

    assert(a.lt(b));
}

#[test]
fn test_field_lte() {
    let a: Field = 2;
    let b: Field = 3;
    let c: Field = 3;

    assert(a.lte(b));
    assert(b.lte(c));
}

#[test]
fn test_field_gt() {
    let a: Field = 2;
    let b: Field = 3;

    assert(b.gt(a));
}

#[test]
fn test_field_gte() {
    let a: Field = 3;
    let b: Field = 2;
    let c: Field = 2;

    assert(a.gte(b));
    assert(b.gte(c));
}

#[test]
fn test_equal() {
    let a: [Field; N] = [2, 0, 0, 0, 0, 0, 0, 0, 0];
    let b: [Field; N] = [2, 0, 0, 0, 0, 0, 0, 0, 0];

    assert(equal(a, b));
}

#[test]
fn test_not_equal() {
    let a: [Field; N] = [2, 0, 0, 0, 0, 0, 0, 0, 0];
    let b: [Field; N] = [3, 0, 0, 0, 0, 0, 0, 0, 0];

    assert(!equal(a, b));
}

#[test]
fn test_less_than() {
    let a: [Field; N] = [2, 0, 0, 0, 0, 0, 0, 0, 0];
    let b: [Field; N] = [3, 0, 0, 0, 0, 0, 0, 0, 0];

    assert(less_than(a, b));
}

#[test]
fn test_less_than_equal() {
    let a: [Field; N] = [2, 0, 0, 0, 0, 0, 0, 0, 0];
    let b: [Field; N] = [3, 0, 0, 0, 0, 0, 0, 0, 0];
    let c: [Field; N] = [3, 0, 0, 0, 0, 0, 0, 0, 0];

    assert(less_than_equal(a, b));
    assert(less_than_equal(b, c));
}

#[test]
fn test_greater_than() {
    let a: [Field; N] = [2, 0, 0, 0, 0, 0, 0, 0, 0];
    let b: [Field; N] = [3, 0, 0, 0, 0, 0, 0, 0, 0];

    assert(greater_than(b, a));
}

#[test]
fn test_greater_than_equal() {
    let a: [Field; N] = [3, 0, 0, 0, 0, 0, 0, 0, 0];
    let b: [Field; N] = [2, 0, 0, 0, 0, 0, 0, 0, 0];
    let c: [Field; N] = [2, 0, 0, 0, 0, 0, 0, 0, 0];

    assert(greater_than_equal(a, b));
    assert(greater_than_equal(b, c));
}

#[test]
fn test_sub() {
    let a: [Field; N] = [0, 1, 0, 0, 0, 0, 0, 0, 0];
    let b: [Field; N] = [1, 0, 0, 0, 0, 0, 0, 0, 0];

    let c = sub(a, b);
    assert(c == [0xffffffffffffffffffffffffffffff, 0, 0, 0, 0, 0, 0, 0, 0]);
}

#[test]
fn test_sub2() {
    let a: [Field; N] = [5, 0, 0, 0, 0, 0, 0, 0, 0];
    let b: [Field; N] = [2, 0, 0, 0, 0, 0, 0, 0, 0];

    let c = sub(a, b);
    assert(c == [3, 0, 0, 0, 0, 0, 0, 0, 0]);
}

#[test]
fn test_sub3() {
    let a: [Field; N] = [
        0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff
    ];
    let b: [Field; N] = [0xffffffffffffffffffffffffffffff, 1, 0, 0, 0, 0, 0, 0, 0];

    let c = sub(a, b);
    assert(
        c == [
            0, 0xfffffffffffffffffffffffffffffe, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff
        ]
    );
}

#[test]
fn test_sub_to_zero() {
    let a: [Field; N] = [1, 0, 0, 0, 0, 0, 0, 0, 0];
    let b: [Field; N] = [1, 0, 0, 0, 0, 0, 0, 0, 0];

    let c = sub(a, b);
    assert(c == [0, 0, 0, 0, 0, 0, 0, 0, 0]);
}

#[test(should_fail_with = "Subtraction underflow")]
fn test_sub_underflow() {
    let a: [Field; N] = [0, 0, 0, 0, 0, 0, 0, 0, 0];
    let b: [Field; N] = [1, 0, 0, 0, 0, 0, 0, 0, 0];

    let c = sub(a, b);
}

#[test]
fn test_add() {
    let a: [Field; N] = [2, 0, 0, 0, 0, 0, 0, 0, 0];
    let b: [Field; N] = [3, 0, 0, 0, 0, 0, 0, 0, 0];

    let c = add(a, b);
    assert(c == [5, 0, 0, 0, 0, 0, 0, 0, 0]);
}

#[test]
fn test_add_carry() {
    let a: [Field; N] = [0xffffffffffffffffffffffffffffff, 0, 0, 0, 0, 0, 0, 0, 0];
    let b: [Field; N] = [2, 0, 0, 0, 0, 0, 0, 0, 0];

    let c = add(a, b);
    assert(c == [1, 1, 0, 0, 0, 0, 0, 0, 0]);
}

#[test]
fn test_add_to_zero() {
    let a: [Field; N] = [0, 0, 0, 0, 0, 0, 0, 0, 0];
    let b: [Field; N] = [3, 0, 0, 0, 0, 0, 0, 0, 0];

    let c = add(a, b);
    assert(c == [3, 0, 0, 0, 0, 0, 0, 0, 0]);
}

#[test]
fn test_mul() {
    let a: [Field; N] = [2, 0, 0, 0, 0, 0, 0, 0, 0];
    let b: [Field; N] = [3, 0, 0, 0, 0, 0, 0, 0, 0];

    let c = normalized_mul(a, b);
    assert(c == [6, 0, 0, 0, 0, 0, 0, 0, 0]);
}

#[test]
fn test_mul2() {
    let a: [Field; N] = [0xffffffffffffffffffffffffffffff, 0, 0, 0, 0, 0, 0, 0, 0];
    let b: [Field; N] = [2, 0, 0, 0, 0, 0, 0, 0, 0];

    let c = normalized_mul(a, b);
    assert(c == [0xfffffffffffffffffffffffffffffe, 1, 0, 0, 0, 0, 0, 0, 0]);
}

#[test]
fn test_mul3() {
    let a: [Field; N] = [0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0, 0, 0, 0, 0, 0, 0];
    let b: [Field; N] = [2, 0, 0, 0, 0, 0, 0, 0, 0];

    let c = normalized_mul(a, b);
    assert(c == [0xfffffffffffffffffffffffffffffe, 0xffffffffffffffffffffffffffffff, 1, 0, 0, 0, 0, 0, 0]);
}

#[test]
fn test_divide() {
    let a: [Field; N] = [15, 0, 0, 0, 0, 0, 0, 0, 0];
    let b: [Field; N] = [3, 0, 0, 0, 0, 0, 0, 0, 0];

    let (q, r) = divide(a, b);

    assert(q == [5, 0, 0, 0, 0, 0, 0, 0, 0]);
    assert(r == [0, 0, 0, 0, 0, 0, 0, 0, 0]);
}

#[test]
fn test_divide_with_remainder() {
    let a: [Field; N] = [13, 0, 0, 0, 0, 0, 0, 0, 0];
    let b: [Field; N] = [2, 0, 0, 0, 0, 0, 0, 0, 0];

    let (q, r) = divide(a, b);

    assert(q == [6, 0, 0, 0, 0, 0, 0, 0, 0]);
    assert(r == [1, 0, 0, 0, 0, 0, 0, 0, 0]);
}

#[test]
fn test_divide_with_large_limb() {
    let a: [Field; N] = [0xffffffffffffffffffffffffffffff, 0, 0, 0, 0, 0, 0, 0, 0];
    let b: [Field; N] = [2, 0, 0, 0, 0, 0, 0, 0, 0];

    let (q, r) = divide(a, b);

    assert(q == [0x7fffffffffffffffffffffffffffff, 0, 0, 0, 0, 0, 0, 0, 0]);
    assert(r == [1, 0, 0, 0, 0, 0, 0, 0, 0]);
}

#[test]
fn test_divide_with_two_limbs() {
    let a: [Field; N] = [0xffffffffffffffffffffffffffffff, 0x1ff, 0, 0, 0, 0, 0, 0, 0];
    let b: [Field; N] = [3, 0, 0, 0, 0, 0, 0, 0, 0];

    let (q, r) = divide(a, b);

    assert(q == [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xaa, 0, 0, 0, 0, 0, 0, 0]);
    assert(r == [1, 0, 0, 0, 0, 0, 0, 0, 0]);
}

#[test]
fn test_divide_with_three_limbs() {
    let a: [Field; N] = [0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0x1ff, 0, 0, 0, 0, 0, 0];
    let b: [Field; N] = [3, 0, 0, 0, 0, 0, 0, 0, 0];

    let (q, r) = divide(a, b);

    assert(
        q
        == [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xaa, 0, 0, 0, 0, 0, 0]
    );
    assert(r == [1, 0, 0, 0, 0, 0, 0, 0, 0]);
}

#[test]
fn test_divide_with_large_biguint() {
    let a: [Field; N] = [
        0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff
    ];
    let b: [Field; N] = [2, 0, 0, 0, 0, 0, 0, 0, 0];

    let (q, r) = divide(a, b);

    assert(
        q == [
            0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0x7fffffffffffffffffffffffffffff
        ]
    );
    assert(r == [1, 0, 0, 0, 0, 0, 0, 0, 0]);
}

#[test]
fn test_divide_with_large_biguint_2() {
    let a: [Field; N] = [
        0xfffffffffffffffffffffffffffffe, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff
    ];
    let b: [Field; N] = [2, 0, 0, 0, 0, 0, 0, 0, 0];

    let (q, r) = divide(a, b);

    assert(
        q == [
            0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0x7fffffffffffffffffffffffffffff
        ]
    );
    assert(r == [0, 0, 0, 0, 0, 0, 0, 0, 0]);
}

#[test]
fn test_divide_with_large_biguint_3() {
    let a: [Field; N] = [
        0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff
    ];
    let b: [Field; N] = [0xffffffffffffffffffffffffffffff, 0, 0, 0, 0, 0, 0, 0, 0];

    let (q, r) = divide(a, b);

    assert(q == [1, 1, 1, 1, 1, 1, 1, 1, 1]);
    assert(r == [0, 0, 0, 0, 0, 0, 0, 0, 0]);
}

#[test]
fn test_divide_with_large_biguint_4() {
    let a: [Field; N] = [
        0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff
    ];
    let b: [Field; N] = [0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0, 0, 0, 0, 0, 0, 0];

    let (q, r) = divide(a, b);

    assert(q == [0, 1, 0, 1, 0, 1, 0, 1, 0]);
    assert(r == [0xffffffffffffffffffffffffffffff, 0, 0, 0, 0, 0, 0, 0, 0]);
}

#[test]
fn test_divide_with_large_biguint_5() {
    let a: [Field; N] = [
        0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff
    ];
    let b: [Field; N] = [
        0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff
    ];

    let (q, r) = divide(a, b);

    assert(q == [1, 0, 0, 0, 0, 0, 0, 0, 0]);
    assert(r == [0, 0, 0, 0, 0, 0, 0, 0, 0]);
}
