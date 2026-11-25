/-! # Base64 (RFC 4648 section 4), as a reference model

Bytes are `Nat`s below 256 and text is a list of code points. `decode` reads only what `encode`
writes: the padding is required and the unused bits of the last character must be zero. -/

namespace Base64

/-- The code point of `=`. -/
def pad : Nat := 61

/-- The character of the 6-bit value `n`. -/
def char (n : Nat) : Nat :=
  if n < 26 then 65 + n
  else if n < 52 then 97 + (n - 26)
  else if n < 62 then 48 + (n - 52)
  else if n = 62 then 43
  else 47

/-- The 6-bit value of the character `c`, or `none` outside the standard alphabet. -/
def value (c : Nat) : Option Nat :=
  if 65 ≤ c ∧ c ≤ 90 then some (c - 65)
  else if 97 ≤ c ∧ c ≤ 122 then some (c - 97 + 26)
  else if 48 ≤ c ∧ c ≤ 57 then some (c - 48 + 52)
  else if c = 43 then some 62
  else if c = 47 then some 63
  else none

def encode : List Nat → List Nat
  | a :: b :: c :: rest =>
    char (a / 4) :: char (a % 4 * 16 + b / 16) :: char (b % 16 * 4 + c / 64) :: char (c % 64)
      :: encode rest
  | [a, b] => [char (a / 4), char (a % 4 * 16 + b / 16), char (b % 16 * 4), pad]
  | [a] => [char (a / 4), char (a % 4 * 16), pad, pad]
  | [] => []

def decode : List Nat → Option (List Nat)
  | [] => some []
  | a :: b :: c :: d :: rest =>
    match value a, value b with
    | some va, some vb =>
      if c = pad then
        if d = pad ∧ rest.isEmpty ∧ vb % 16 = 0 then some [va * 4 + vb / 16] else none
      else
        match value c with
        | none => none
        | some vc =>
          if d = pad then
            if rest.isEmpty ∧ vc % 4 = 0 then some [va * 4 + vb / 16, vb % 16 * 16 + vc / 4]
            else none
          else
            match value d with
            | none => none
            | some vd =>
              (decode rest).map fun r =>
                (va * 4 + vb / 16) :: (vb % 16 * 16 + vc / 4) :: (vc % 4 * 64 + vd) :: r
    | _, _ => none
  | _ => none

theorem value_char : ∀ n, n < 64 → value (char n) = some n := by decide

theorem char_ne_pad : ∀ n, n < 64 → char n ≠ pad := by decide

theorem decode_encode (bs : List Nat) (h : ∀ x ∈ bs, x < 256) : decode (encode bs) = some bs := by
  fun_induction encode bs with
  | case1 a b c rest ih =>
    have ha := h a (by simp); have hb := h b (by simp); have hc := h c (by simp)
    have ih := ih (fun x hx => h x (by simp [hx]))
    simp only [decode, value_char _ (by omega : a / 4 < 64),
      value_char _ (by omega : a % 4 * 16 + b / 16 < 64),
      value_char _ (by omega : b % 16 * 4 + c / 64 < 64), value_char _ (by omega : c % 64 < 64),
      char_ne_pad _ (by omega : b % 16 * 4 + c / 64 < 64), char_ne_pad _ (by omega : c % 64 < 64),
      ite_false, ih, Option.map_some, Option.some.injEq, List.cons.injEq]
    exact ⟨by omega, by omega, by omega, trivial⟩
  | case2 a b =>
    have ha := h a (by simp); have hb := h b (by simp)
    simp only [decode, value_char _ (by omega : a / 4 < 64),
      value_char _ (by omega : a % 4 * 16 + b / 16 < 64),
      value_char _ (by omega : b % 16 * 4 < 64), char_ne_pad _ (by omega : b % 16 * 4 < 64)]
    simp [List.isEmpty]
    omega
  | case3 a =>
    have ha := h a (by simp)
    simp only [decode, value_char _ (by omega : a / 4 < 64),
      value_char _ (by omega : a % 4 * 16 < 64)]
    simp [List.isEmpty]
    omega
  | case4 => rfl

theorem char_value {c v : Nat} (h : value c = some v) : v < 64 ∧ char v = c := by
  unfold value at h
  repeat' split at h
  all_goals (try cases h)
  all_goals (refine ⟨by omega, ?_⟩; unfold char; repeat' split)
  all_goals omega

/-- `decode` accepts only what `encode` writes. -/
theorem encode_decode (cs bs : List Nat) (h : decode cs = some bs) : encode bs = cs := by
  fun_induction decode cs generalizing bs with
  | case1 => cases h; rfl
  | case2 a b d rest va vb hb ha hc =>
    obtain ⟨hva, rfl⟩ := char_value ha
    obtain ⟨hvb, rfl⟩ := char_value hb
    obtain ⟨rfl, hr, hm⟩ := hc
    rw [List.isEmpty_iff] at hr
    subst hr
    cases h
    simp only [encode]
    rw [show (va * 4 + vb / 16) / 4 = va by omega, show (va * 4 + vb / 16) % 4 * 16 = vb by omega]
  | case5 a b c rest va vb hb ha hcp vc hvc hcond =>
    obtain ⟨hva, rfl⟩ := char_value ha
    obtain ⟨hvb, rfl⟩ := char_value hb
    obtain ⟨hvc', rfl⟩ := char_value hvc
    obtain ⟨hr, hm⟩ := hcond
    rw [List.isEmpty_iff] at hr
    subst hr
    cases h
    simp only [encode]
    rw [show (va * 4 + vb / 16) / 4 = va by omega,
      show (va * 4 + vb / 16) % 4 * 16 + (vb % 16 * 16 + vc / 4) / 16 = vb by omega,
      show (vb % 16 * 16 + vc / 4) % 16 * 4 = vc by omega]
  | case8 a b c d rest va vb hb ha hcp vc hvc hdp vd hvd ih =>
    obtain ⟨hva, rfl⟩ := char_value ha
    obtain ⟨hvb, rfl⟩ := char_value hb
    obtain ⟨hvc', rfl⟩ := char_value hvc
    obtain ⟨hvd', rfl⟩ := char_value hvd
    cases hr : decode rest with
    | none => simp [hr] at h
    | some r =>
      simp only [hr, Option.map_some, Option.some.injEq] at h
      subst h
      simp only [encode, ih r hr]
      rw [show (va * 4 + vb / 16) / 4 = va by omega,
        show (va * 4 + vb / 16) % 4 * 16 + (vb % 16 * 16 + vc / 4) / 16 = vb by omega,
        show (vb % 16 * 16 + vc / 4) % 16 * 4 + (vc % 4 * 64 + vd) / 64 = vc by omega,
        show (vc % 4 * 64 + vd) % 64 = vd by omega]
  | _ => cases h

end Base64
