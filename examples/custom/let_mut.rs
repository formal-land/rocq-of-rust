fn let_mut() -> i32 {
  let mut x = 5;
  x = x + 1;
  x
}

fn match_mut() -> i32 {
  let Some(mut x) = Some(5) else {
    return 0;
  };
  x = x + 1;
  x
}
