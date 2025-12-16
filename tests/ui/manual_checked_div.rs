#![warn(clippy::manual_checked_div)]

fn main() {
    let a = 10u32;
    let b = 5u32;

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

    let c = -5i32;
    if c != 0 {
        //~^ manual_checked_div
        let _result = 10 / c;
    }
}
