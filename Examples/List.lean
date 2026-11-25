/-! # Basic list functions

The model is Lean's own `List` at `Nat`. Each law that the property tests of Emela's `List`
(`tests/laws/test/list_test.emel` in the Emela repository) check on samples is a theorem here. -/

namespace ListModel

def reverse (xs : List Nat) : List Nat := xs.reverse

def append (xs ys : List Nat) : List Nat := xs ++ ys

def take (xs : List Nat) (n : Nat) : List Nat := xs.take n

def drop (xs : List Nat) (n : Nat) : List Nat := xs.drop n

def length (xs : List Nat) : Nat := xs.length

def sort (xs : List Nat) : List Nat := xs.mergeSort (fun a b => decide (a ≤ b))

/-! ## reverse and append -/

theorem reverse_reverse (xs : List Nat) : reverse (reverse xs) = xs := by
  simp [reverse]

theorem length_reverse (xs : List Nat) : length (reverse xs) = length xs := by
  simp [length, reverse]

theorem append_nil (xs : List Nat) : append xs [] = xs := by
  simp [append]

theorem nil_append (xs : List Nat) : append [] xs = xs := by
  simp [append]

theorem length_append (xs ys : List Nat) : length (append xs ys) = length xs + length ys := by
  simp [length, append]

theorem reverse_append (xs ys : List Nat) :
    reverse (append xs ys) = append (reverse ys) (reverse xs) := by
  simp [reverse, append]

/-! ## take and drop -/

theorem take_append_drop (xs : List Nat) (n : Nat) : append (take xs n) (drop xs n) = xs := by
  simp [append, take, drop]

/-! ## sort -/

/-- The result is in order. `mergeSort` needs only that `≤` is transitive and total. -/
theorem sort_sorted (xs : List Nat) : (sort xs).Pairwise (fun a b => decide (a ≤ b)) :=
  List.pairwise_mergeSort
    (fun a b c hab hbc => by simp at *; omega)
    (fun a b => by simp; omega)
    xs

/-- The result has the same elements, each as many times. -/
theorem sort_perm (xs : List Nat) : (sort xs).Perm xs :=
  List.mergeSort_perm xs _

theorem length_sort (xs : List Nat) : length (sort xs) = length xs :=
  (sort_perm xs).length_eq

/-- Sorting a sorted list changes nothing. -/
theorem sort_sort (xs : List Nat) : sort (sort xs) = sort xs :=
  List.mergeSort_of_pairwise (sort_sorted xs)

end ListModel
