/-! # A binary search tree, to exercise inductive types at the boundary -/

namespace Tree

inductive Tree (α : Type) where
  | leaf
  | node (left : Tree α) (key : α) (right : Tree α)

def insert (t : Tree Nat) (x : Nat) : Tree Nat :=
  match t with
  | .leaf => .node .leaf x .leaf
  | .node l k r => if x < k then .node (insert l x) k r else if k < x then .node l k (insert r x) else t

def fromList (xs : List Nat) : Tree Nat := xs.foldl insert .leaf

def toList : Tree Nat → List Nat
  | .leaf => []
  | .node l k r => toList l ++ k :: toList r

def find? (t : Tree Nat) (x : Nat) : Option Nat :=
  match t with
  | .leaf => none
  | .node l k r => if x < k then find? l x else if k < x then find? r x else some k

/-! ## What the model guarantees -/

/-- A key that was inserted is found. -/
theorem find?_insert_self (t : Tree Nat) (x : Nat) : find? (insert t x) x = some x := by
  induction t with
  | leaf => simp [insert, find?]
  | node l k r ihl ihr =>
    unfold insert
    by_cases hlt : x < k
    · -- `x` goes to the left, and is looked up on the left.
      simp [hlt, find?, ihl]
    · by_cases hgt : k < x
      · -- `x` goes to the right, and is looked up on the right.
        simp [hlt, hgt, find?, ihr]
      · -- `x` is the key of this node: the tree is unchanged, and the key is found here.
        have hx : x = k := by omega
        simp [hx, find?]

/-- Inserting `y` adds `y` to the keys and keeps the others. -/
theorem mem_toList_insert (t : Tree Nat) (x y : Nat) :
    x ∈ toList (insert t y) ↔ x = y ∨ x ∈ toList t := by
  induction t with
  | leaf => simp [insert, toList]
  | node l k r ihl ihr =>
    unfold insert
    by_cases hlt : y < k
    · -- `y` goes to the left subtree.
      simp [hlt, toList, ihl, or_assoc, or_left_comm]
    · by_cases hgt : k < y
      · -- `y` goes to the right subtree.
        simp [hlt, hgt, toList, ihr, or_left_comm]
      · -- `y` is already the key of this node, so the tree is unchanged.
        have hy : y = k := by omega
        by_cases hx : x = k <;> simp [hy, hx, toList]

/-- Folding `insert` over `xs` adds exactly the elements of `xs`. -/
theorem mem_toList_foldl (xs : List Nat) (t : Tree Nat) (x : Nat) :
    x ∈ toList (xs.foldl insert t) ↔ x ∈ xs ∨ x ∈ toList t := by
  induction xs generalizing t with
  | nil => simp
  | cons y ys ih =>
    simp [List.foldl, ih, mem_toList_insert, or_assoc, or_left_comm]

/-- The keys of `fromList xs` are exactly the elements of `xs`. -/
theorem mem_toList_fromList (xs : List Nat) (x : Nat) : x ∈ toList (fromList xs) ↔ x ∈ xs := by
  simp [fromList, mem_toList_foldl, toList]

end Tree
