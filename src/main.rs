// Actual size in bits of the number
const L: usize = 256;
// Number of bits per limb
const D: usize = 64;
// Take the ceiling of L/D
const N: usize = (L + D - 1) / D;
// 2^128 - 1
const P: [u128; N] = [0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0, 0];

fn biguint_equal<const SIZE : usize>(x: &[u128; SIZE], y: &[u128; SIZE]) -> bool {
    for i in 0..SIZE {
        if x[i] != y[i] {
            return false;
        }
    }
    true
}

fn biguint_less_than<const SIZE : usize>(x: &[u128; SIZE], y: &[u128; SIZE]) -> bool {
    for i in (0..SIZE).rev() {
        if x[i] < y[i] {
            return true;
        } else if x[i] > y[i] {
            return false;
        }
    }
    false
}

fn biguint_less_than_or_equal<const SIZE : usize>(x: &[u128; SIZE], y: &[u128; SIZE]) -> bool {
    for i in (0..SIZE).rev() {
        if x[i] < y[i] {
            return true;
        } else if x[i] > y[i] {
            return false;
        }
    }
    true
}

fn biguint_greater_than<const SIZE : usize>(x: &[u128; SIZE], y: &[u128; SIZE]) -> bool {
    !biguint_less_than_or_equal(x, y)
}

fn biguint_greater_than_or_equal<const SIZE : usize>(x: &[u128; SIZE], y: &[u128; SIZE]) -> bool {
    !biguint_less_than(x, y)
}

fn biguint_to_bits<const SIZE : usize>(x: &[u128; SIZE]) -> Vec<u8> {
    let mut bits = Vec::new();
    for i in (0..SIZE).rev() {
        for j in (0..D).rev() {
            bits.push((x[i] >> j) as u8 & 1);
        }
    }
    bits
}

fn biguint_bits_count<const SIZE : usize>(x: &[u128; SIZE]) -> usize {
    let mut count = 0;
    let bits = biguint_to_bits(x);
    let len = bits.len();
    for i in 0..len {
        if bits[i] != 0 {
            count = len - i;
            break;
        }
    }
    count
}

fn sbb(x: u128, y: u128, borrow: u128) -> (u128, u128) {
    let (diff, borrow1) = x.overflowing_sub(y);
    let (diff, borrow2) = diff.overflowing_sub(borrow);
    let borrow = if borrow1 || borrow2 { 1 } else { 0 };
    (diff, borrow)
}

fn biguint_sub<const SIZE : usize>(x: &[u128; SIZE], y: &[u128; SIZE]) -> [u128; SIZE] {
    let mut res = [0; SIZE];
    let mut borrow = 0;

    for i in 0..N {
        let (diff, new_borrow) = sbb(x[i], y[i], borrow);
        res[i] = diff;
        borrow = new_borrow;
    };
    
    res
}

fn adc(x: u128, y: u128, carry: u64) -> (u128, u64) {
    let sum = x as u64 + y as u64 + carry;
    let carry = if sum > u64::MAX { 1 } else { 0 };
    (sum as u128, carry)
}

fn biguint_add<const SIZE : usize>(x: &[u128; SIZE], y: &[u128; SIZE]) -> [u128; SIZE] {
    let mut res = [0; SIZE];
    let mut carry = 0 as u64;

    for i in 0..SIZE {
        let (sum, new_carry) = adc(x[i], y[i], carry);
        res[i] = sum;
        carry = new_carry;
    };

    res
}

fn biguint_shift_left_limb<const SIZE : usize>(x: &[u128; SIZE], n: u64) -> ([u128; SIZE], u128) {
    let mut res = x.clone();

    let rshift = D as u64 - n;
    let carry = if n == 0 { 0 } else { x[SIZE - 1] >> rshift };

    if n > 0 {
        res[0] = x[0] << n;
        for i in 1..SIZE {
            res[i] = (x[i] << n) | (x[i - 1] >> rshift);
        }
    }

    (res, carry)
}

/// Shifts the LargeInteger instance to the left by a specified number of bits `n`.
fn biguint_shift_left<const SIZE : usize>(x: &[u128; SIZE], n: u64) -> [u128; SIZE] {
    let mut res = [0; SIZE];

    if n < L as u64 {
        let shift_num = n / (D as u64);
        let rem = n % (D as u64);
        
        for i in shift_num..SIZE as u64 { 
            res[i as usize] = x[i as usize - shift_num as usize];
        }

        let (new_lower, _carry) = biguint_shift_left_limb(&res, rem);
        res = new_lower;
    }

    res
}

fn biguint_shift_right_limb<const SIZE : usize>(x: &[u128; SIZE], n: u64) -> [u128; SIZE] {
    let mut res = x.clone();

    if n > 0 {
        let lshift = D as u64 - n;

        for i in 0..SIZE-1 {
            res[i] = (x[i] >> n) | (x[i + 1] << lshift);
        }
        res[SIZE - 1] = x[SIZE - 1] >> n;
    }


    res
}

fn biguint_shift_right<const SIZE : usize>(x: &[u128; SIZE], n: u64) -> [u128; SIZE] {
    let mut res = [0; SIZE];

    if n < L as u64 {
        let shift_num = n / (D as u64);
        let rem = n % (D as u64);

        // for i in 0..shift_num {
        for i in 0..N {
            if i as u64 + shift_num < N as u64 {
                res[i] = x[i as usize + shift_num as usize];
            }
        }

        res = biguint_shift_right_limb(&res, rem);
    }

    res
}


fn biguint_divide<const SIZE : usize>(x: &[u128; SIZE], y: &[u128; SIZE]) -> ([u128; SIZE], [u128; SIZE]){
    if biguint_less_than(x, y) {
        return ([0; SIZE], x.clone());
    }

    let mut q = [0; SIZE];
    let mut r = x.clone();
    let bit_diff = biguint_bits_count(x) - biguint_bits_count(y);
    let mut c = biguint_shift_left(y, bit_diff as u64);

    let mut one = [0; SIZE];
    one[0] = 1;

    for i in 0..L+1 {
        if i <= bit_diff {
            if biguint_greater_than_or_equal(&r, &c) {
                r = biguint_sub(&r, &c);
                q = biguint_shift_left(&q, 1);
                q = biguint_add(&q, &one);
            } else {
                q = biguint_shift_left(&q, 1);
            }
            c = biguint_shift_right(&c, 1);
        }
    };

    (q, r)
}

fn compute_product(a: &[u128; N], b: &[u128; N]) -> [u128; N * 2 - 1] {
    let mut a_times_b = [0; N * 2 - 1];
    for i in 0..(N * 2 - 1) {
        for j in 0..=i {
            if j < N && i - j < N {
                a_times_b[i] += a[j] * b[i - j];
            }
        }
    }

    // How many times does the a_times_b fit into P?
    /*let (q, c) = biguint_divide(&a_times_b, &[P[0], P[1], 0, 0, 0, 0, 0]);

    let p_times_q = biguint_multiply(&[P[0], P[1], 0, 0, 0, 0, 0], &q);

    let output = biguint_sub(&c, &biguint_sub(&a_times_b, &p_times_q));
    output*/
    a_times_b
}

fn biguint_multiply<const SIZE : usize>(x: &[u128; SIZE], y: &[u128; SIZE]) -> [u128; SIZE] {
    let mut z = [0; SIZE];
    let mut tmp: [u128; N * 4] = [0; N * 4];
    let mut carry: u128 = 0;
    for i in 0..SIZE {
        for j in 0..SIZE {
            let res = (x[i] as u128) * (y[j] as u128) + (tmp[i + j] as u128) + carry;
            let lo = res % (1 << D);
            let hi = (res >> D) % (1 << D);
            tmp[i + j] = lo;
            tmp[i + j + 1] = hi;
            carry = hi as u128 >> D;
        }
    }
    for i in 0..SIZE {
        z[i] = tmp[i] + carry;
        carry = 0;
    }
    z
}

fn biguint_karatsuba_multiply(x: &[u128; N], y: &[u128; N]) -> [u128; N] {
    [0; N]
}

fn to_string(x: &[u128]) -> String {
    let mut s = String::new();
    let mut i = N - 1;
    while i > 0 && x[i] == 0 {
        i -= 1;
    }
    s.push_str(&x[i].to_string());
    while i > 0 {
        i -= 1;
        s.push_str(&format!("{:0>64}", x[i]));
    }
    s
}

fn main() {
    let x: [u128; N] = [4, 0, 0, 0];
    let y: [u128; N] = [2, 0, 0, 0];
    let z: [u128; N * 2 - 1] = compute_product(&x, &y);
    let (q, r) = biguint_divide(&x, &y);
    println!("x = {}", to_string(&x));
    println!("y = {}", to_string(&y));
    println!("z = {}", to_string(&z));
    println!("q = {}", to_string(&q));
    println!("r = {}", to_string(&r));
}