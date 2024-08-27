use tp2_rs::{List, list};
fn main() {
    let list1 = list!(1, 2, 3, 4, 5, 7);
    list1.iter().map(|n| n * 2).for_each(|n| println!("{}", n));
    println!("Sum: {}", list1.iter().sum::<i32>());
    println!("Product: {}", list1.iter().product::<i32>());
    println!("Max: {}", list1.iter().max().unwrap());
    println!("Min: {}", list1.iter().min().unwrap());
    println!("Count: {}", list1.iter().count());
    println!("list: {}", list1);

    let mut list2 = list!(1, 2, 3, 4, 5, 7);

    {
        let mut list_iter = list2.iter_mut();
        list_iter.insert_after(10);
        println!("list: {}", list2);
    }
    {
        let mut list_iter = list2.iter_mut();
        list_iter.next();
        list_iter.insert_before(23);
        println!("list: {}", list2);
    }
    
}
