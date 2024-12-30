module P6

/// From list 'l', find the element that appears most frequently in the list,
/// and return how many times it appears. If the input list is empty, return 0.
let rec countMostFrequent (l: List<'a>) : int =
  match l with
  | [] -> 0
  | head :: tail ->
      let dict = List.countBy (fun x -> x) l // (key,int) list
      let max_key = List.fold (fun x (key,count) -> if x < count then count else x) 0 dict 
      max_key
