// Actual size in bits of the number
const L: usize = 256;
// Number of bits per limb
// We set it to 32 bits while operating on u128 to simulate working with 
// with 120-bit limbs over a field size of 254 bits like in Noir.
// We can't use 64 bits as the multiplication result can have limbs of size
// 2 * D + ceil(log2(N)) which can be greater than 128 bits.
// e.g. For D = 64 and N = 4, the multiplication result can have 
// limbs of size 2 * 64 + ceil(log2(4)) = 130 bits.
const D: usize = 32;
// Take the ceiling of L/D
// 256 / 32 = 8 limbs
const N: usize = (L + D - 1) / D;
// 2^128 - 1
const P: [u128; N] = [0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0, 0, 0, 0];
// 2^32 to constrain the limb size
const LIMB_MODULO: u128 = (2 as u128).pow(D as u32);

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
    for i in 0..SIZE {
        let max_non_zero_index = 128 - x[i].leading_zeros();
        for j in 0..max_non_zero_index {
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

    for i in 0..SIZE {
        let (diff, new_borrow) = sbb(x[i], y[i], borrow);
        res[i] = diff;
        borrow = new_borrow;
    };
    
    res
}

fn adc(x: u128, y: u128, carry: u128) -> (u128, u128) {
    let sum = x + y  + carry;
    let carry = if sum >= LIMB_MODULO { 1 } else { 0 };
    ((sum % LIMB_MODULO) as u128, carry)
}

fn biguint_add<const SIZE : usize>(x: &[u128; SIZE], y: &[u128; SIZE]) -> [u128; SIZE] {
    let mut res = [0; SIZE];
    let mut carry = 0 as u128;

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
        /*
         * Example:
         * Let x = 0b1110110111010111 be a 16-bit number represented as two 8 bits limbs in little-endian order
         * like so: [0b11010111, 0b11101101].
         * We shift x by n = 5 bits to the left -> x << 5.
         * For the first limb, we have:
         * 0b11010111 << 5 = 0b11100000
         * For the second limb, we have:
         * 0b11101101 << 5 = 0b10100000
         * But doing the left shift of the first limb, we lost its 5 leftmost bits, thus we need to carry
         * them over the following higher significance limb. Each limb has 8 bits, and since we want 
         * the 5 original leftmost (most significants) bits of the first limb to be passed on the 5 rightmost 
         * (least significants) bits of the second higher limb, we need to shift the first limb to 
         * the right by 8 - 5 = 3 bits. Which give us: 0b11010111 >> 3 = 0b00011010. 
         * We then OR this result with the left shifted second limb to combine the two 
         * and get: 0b00011010 | 0b10100000 = 0b10111010.
         * Which give us the final result: 0b1011101011100000 or in the limbs representation: [0b11100000, 0b10111010].
         */
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
        for i in 0..SIZE {
            if i as u64 + shift_num < SIZE as u64 {
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
    let mut c = biguint_shift_left(&y, bit_diff as u64);

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

fn biguint_to_binary_string<const SIZE : usize>(x: &[u128; SIZE]) -> String {
    let mut s = String::new();
    for i in (0..SIZE).rev() {
        s.push_str(&format!("{:032b}", x[i]));
    }
    s
}

fn biguint_to_hex_string<const SIZE : usize>(x: &[u128; SIZE]) -> String {
    let mut s = String::new();
    for i in (0..SIZE).rev() {
        s.push_str(&format!("{:08x}", x[i]));
    }
    s
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
    let (q, c) = biguint_divide(&a_times_b, &[P[0], P[1], P[2], P[3], 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    println!("q = {}", biguint_to_hex_string(&q));
    println!("c = {}", biguint_to_hex_string(&c));

    let p_times_q = biguint_multiply(&[P[0], P[1], P[2], P[3], 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], &q);
    println!("p_times_q = {}", biguint_to_hex_string(&p_times_q));

    let output = biguint_sub(&c, &biguint_sub(&a_times_b, &p_times_q));
    println!("output = {}", biguint_to_hex_string(&output));
    //output
    a_times_b
}

fn main() {
    let x: [u128; N] = [0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0, 0, 0, 0];
    println!("x = {}", biguint_to_hex_string(&x));
    let y: [u128; N] = [0xffffffff, 0, 0, 0, 0, 0, 0, 0];
    println!("y = {}", biguint_to_hex_string(&y));
    let o: [u128; N * 2 - 1] = compute_product(&x, &y);
    println!("o = {:?}", o);

    let mut r: [i128;  N * 2 - 1] = [0; N * 2 - 1];
    r[0] = (o[0] / LIMB_MODULO) as i128;
    for i in 1..(N * 2 - 2) {
        r[i] = (o[i]  as i128  - r[i - 1] as i128) / LIMB_MODULO as i128 ;
    }
    r[N * 2 - 2] = o[N * 2 - 2] as i128 - r[N * 2 - 3];
    println!("r = {:?}", r);

    /*let (q, _r) = biguint_divide(&x, &y);
    println!("q = {}", biguint_to_hex_string(&q));
    println!("_r = {}", biguint_to_hex_string(&_r));*/
}