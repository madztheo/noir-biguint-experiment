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

    res
}

// We assume each Field is less than 128 bits
fn shl_limb<SIZE>(val: [Field; SIZE], n: u8) -> ([Field; SIZE], u64) {
    assert(n < D as u8);

    let mut res = val;

    let rshift: u8 = D as u8 - n;
    let carry = if (n == 0) { 0 } else { (U128::from_integer(val[N - 1]) >> rshift).to_integer() };

    if (n > 0) {
        res[0] = (U128::from_integer(val[0]) << n).to_integer();
        for i in 1..N {
            res[i] = ((U128::from_integer(val) << n) | (U128::from_integer(val[i - 1]) >> rshift)).to_integer();
        }
    }

    (res, carry)
}

// We assume each Field is less than 128 bits
fn shl<SIZE>(val: [Field; SIZE], n: u8) -> [Field; SIZE] {
    let mut res = [0; SIZE];

    if n as u64 < L {
        let shift_num = n / D as u8;
        let rem = n % D as u8;
        
        for i in shift_num..N as u8 {
            res[i] = val[i - shift_num];
        }

        let (new_lower, _carry) = shl_limb(res, rem);
        res = new_lower;
    }

    res
}

// We assume each Field is less than 128 bits
fn shr_limb<SIZE>(val: [Field; SIZE], n: u8) -> [Field; SIZE] {
    assert(n < D as u8);

    let mut res = val;

    if (n > 0) {
        let lshift = D as u8 - n;

        for i in 0..N-1 {
            res[i] = ((U128::from_integer(val[i]) >> n) | (U128::from_integer(val[i + 1]) << lshift)).to_integer();
        }
        res[N - 1] = (U128::from_integer(val[N - 1]) >> n).to_integer();
    }

    res
}

// We assume each Field is less than 128 bits
fn shr<SIZE>(val: [Field; SIZE], n: u8) -> [Field; SIZE] {
    let mut res = [0; SIZE];

    if n < L as u8 {
        let shift_num = n / D as u8;
        let rem = n % D as u8;

        // for i in 0..shift_num {
        for i in 0..N as u8 {
            if i + shift_num < N as u8 {
                res[i] = val[i + shift_num];
            }
        }

        res = shr_limb(res, rem);
    }

    res
}

fn less_than<SIZE>(x: [Field; SIZE], y: [Field; SIZE]) -> bool {
    let mut res = false;
    for i in 0..SIZE {
        if x[SIZE - i - 1].lt(y[SIZE - i - 1]) {
            res = true;
        }
    }

    res
}

fn less_than_equal<SIZE>(x: [Field; SIZE], y: [Field; SIZE]) -> bool {
    let mut res = false;
    for i in 0..SIZE {
        if (x[SIZE - i - 1].lt(y[SIZE - i - 1])) | (x[SIZE - i - 1] == y[SIZE - i - 1]) {
            res = true;
        }
    }

    res
}

fn greater_than<SIZE>(x: [Field; SIZE], y: [Field; SIZE]) -> bool {
    less_than(y, x)
}

fn greater_than_equal<SIZE>(x: [Field; SIZE], y: [Field; SIZE]) -> bool {
    less_than_equal(y, x)
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
    assert(less_than(y, x), "Subtraction underflow");

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

fn normalized_mul<SIZE>(x: [Field; SIZE], y: [Field; SIZE]) -> [Field; SIZE] {
    // TODO: Implement multiplication of two big int
    let mut c: [Field; 2 * N] = [0; 2 * N];
    let m = nlimbs(x);
    let n = nlimbs(y);
    let k = m + n;
    let mut r: Field = 0;
    
    for i in 0..SIZE {
        for j in 0..SIZE {
            let s: Field = x[j] * y[i] + c[i + j] + r;
            // TODO: Find a way to do it without using U128
            c[i + j] = (U128::from_integer(s) % U128::from_integer(B)).to_integer();
            r = (U128::from_integer(s) / U128::from_integer(B)).to_integer();
        }
        c[i+m] += r;
    }

    let mut normalized_c = [0; SIZE];
    
    for i in 0..SIZE {
        normalized_c[i] = c[i];
    }

    normalized_c
}

fn find_quotient_limb<SIZE>(r: [Field; SIZE], b: [Field; SIZE]) -> Field {
    // TODO: Implement Algorithm in 4.1 
    // c.f. https://people.eecs.berkeley.edu/~fateman/282/F%20Wright%20notes/week4.pdf
    let mut q = [0; SIZE];
    q[0] = B - 1;
    let mut r = sub(r, normalized_mul(b, q));

    /*for i in 0..B {
        if r[0].gt(0) {
            q[0] = q[0] - 1;
            r = add(r, b);
        }
    }*/
    
    q[0]
}

// c.f. https://people.eecs.berkeley.edu/~fateman/282/F%20Wright%20notes/week4.pdf - Algorithm in 4
unconstrained fn divide<SIZE>(x: [Field; SIZE], y: [Field; SIZE]) -> ([Field; SIZE], [Field; SIZE]){
    if less_than(x, y) {
        ([0; SIZE], x)
    }

    // Quotient
    let mut q = [0; SIZE];

    let m = nlimbs(x);
    let n = nlimbs(y);
    let k = m - n + 1;

    // Remainder
    // TODO: Find a way to handle the proper size of r
    let mut r = [0; SIZE];

    for i in 1..n {
        r[i] = x[i-1];
    }

    for i in 0..k {
        q[i] = find_quotient_limb(r, y);
        let mut q_i_long = [0; SIZE];
        q_i_long[i] = q[i];
        r = sub(r, normalized_mul(q_i_long, y));
        if i != k - 1 {
            r[n] = x[m - k + 1 + i];
        }
    }
    
    (q, r)
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
    let a: [Field; N] = [0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff];
    let b: [Field; N] = [0xffffffffffffffffffffffffffffff, 1, 0, 0, 0, 0, 0, 0, 0];

    let c = sub(a, b);
    assert(c == [0, 0xfffffffffffffffffffffffffffffe, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffff]);
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

/*#[test]
fn test_divide() {
    let a: [Field; N] = [6, 0, 0, 0, 0, 0, 0, 0, 0];
    let b: [Field; N] = [2, 0, 0, 0, 0, 0, 0, 0, 0];

    let (q, r) = divide(a, b);
    println(q);
    println(r);

    // TODO: Test that the result of the division is correct
}*/