#![warn(clippy::manual_checked_div)]

fn main() {
    let a = 10u32;
    let mut b = 5u32;

    // Should trigger lint
    if b != 0 {
        //~^ manual_checked_div
        let _result = a / b;
        let _another = (a + 1) / b;
    }

    if b > 0 {
        //~^ manual_checked_div
        let _result = a / b;
    }

    if b == 0 {
        //~^ manual_checked_div
        println!("zero");
    } else {
        let _result = a / b;
    }

    // Should NOT trigger (already using checked_div)
    if let Some(result) = b.checked_div(a) {
        println!("{result}");
    }

    // Should NOT trigger (signed integers are not linted)
    let c = -5i32;
    if c != 0 {
        let _result = 10 / c;
    }

    // Should NOT trigger (side effects in divisor)
    if counter() > 0 {
        let _ = 32 / counter();
    }

    // Should NOT trigger (divisor used before division)
    if b > 0 {
        use_value(b);
        let _ = a / b;
    }

    let signed_min = i32::MIN;
    let mut signed_div: i32 = -1;

    // Should NOT trigger (signed integers are not linted)
    if signed_div != 0 {
        let _ = signed_min / signed_div;
    }

    signed_div = 2;

    if signed_div > 0 {
        let _ = signed_min / signed_div;
    }

    // Should NOT trigger (divisor may change during evaluation)
    if b > 0 {
        g(inc_and_return_value(&mut b), a / b);
    }
}

fn counter() -> u32 {
    println!("counter");
    1
}

fn use_value(_v: u32) {}

fn inc_and_return_value(x: &mut u32) -> u32 {
    *x += 1;
    *x
}

fn g(_lhs: u32, _rhs: u32) {}

fn arbitrary_signed(lhs: i32, rhs: i32) -> i32 {
    if rhs != 0 { lhs / rhs } else { lhs }
}

fn arbitrary_unsigned(lhs: u32, rhs: u32) -> u32 {
    if rhs != 0 {
        //~^ manual_checked_div
        lhs / rhs
    } else {
        lhs
    }
}
