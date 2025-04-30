/-
Copyright (c) 2025 Edward van de Meent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward van de Meent
-/
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Rel
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.OrderIsoNat
import Mathlib.Data.List.Destutter


/-!
# Series of a relation

If `r` is a relation on `α` then a relation series of length `n` is a series
`a_0, a_1, ..., a_n` such that `r a_i a_{i+1}` for all `i < n`

-/

variable {α : Type*} (r : Rel α α)

/-- `a -[r]→* b` is a type of nonempty lists of elements such that adjacent elements are
  related by `r`, and such that the list starts/ends with `a`/`b` respectively. -/
inductive RelSeriesHT {α : Type*} (r :α → α → Sort*): (a : α) → (b : α) → Sort (max (u_2 + 1) u_3)
where
  | singleton (a : α) : RelSeriesHT r a a
  | cons (a : α) {b c: α} (l : RelSeriesHT r b c) (hab : r a b) : RelSeriesHT r a c

variable {r}
namespace RelSeriesHT
/-- notation for `RelSeriesHT` -/
scoped notation3 l " -[" rel "]→* " r:arg => RelSeriesHT rel l r


/-- the first element of an `r`-series -/
def head {a _b : α} (_l :a -[r]→* _b) : α := a
-- (a,b)[r]

@[simp]
lemma head_singleton {a : α} : head (.singleton (r := r) a) = a := rfl

@[simp]
lemma head_cons {a b c : α} (l : b -[r]→* c) (hab : r a b) :
  head (.cons a l hab) = a := rfl

/-- End of a series, i.e. for `a₀ -r→ a₁ -r→ ... -r→ aₙ`, its last element is `aₙ`.
  Since a relation series is assumed to be non-empty, this is well defined. -/
def getLast {a b : α} (_l : a -[r]→* b) : α := b

@[simp]
lemma getLast_singleton {a : α} : getLast (.singleton (r := r) a) = a := rfl

@[simp]
lemma getLast_cons {a b c : α} (l : b -[r]→* c) (hab : r a b) :
  getLast (.cons a l hab) = getLast l := rfl

/-- the coercion of an `r`-series given by listing the elements -/
def toList {a b : α} (l : a -[r]→* b) : List α :=
  match l with
  | .singleton a => [a]
  | .cons a l' h => a::toList l'

@[simp]
lemma toList_singleton {a : α} : toList (.singleton (r := r) a) = [a] := rfl

@[simp]
lemma toList_cons (a : α) {b c : α} (l : b -[r]→* c) (hab : r a b) :
    toList (.cons a l hab) = a::toList l := rfl

@[simp]
lemma toList_ne_nil {a b : α} (l : a -[r]→* b) : l.toList ≠ [] := by
  cases l <;> simp

@[simp]
lemma head_toList {a b : α} (l : a -[r]→* b) (hl : toList l ≠ [] := l.toList_ne_nil) :
    l.toList.head hl = a := by
  cases l <;> rfl

@[simp]
lemma getLast_toList {a b : α} (l : a -[r]→* b) (hl : toList l ≠ [] := l.toList_ne_nil) :
    l.toList.getLast hl = b := by
  induction l <;> simp_all

lemma chain'_toList {a b : α} (l : a -[r]→* b) : l.toList.Chain' r := by
  induction l with
  | singleton a => simp
  | cons a l hab ih => simp_all [List.chain'_cons', List.head?_eq_head l.toList_ne_nil]

-- lemma toList_eq_append {a b : α} (l : a -[r]→* b) (x y : List α) :
-- z

-- @[ext] doesn't work here
lemma ext {a a' b b' : α} (l : a -[r]→* b) (l' : a' -[r]→* b') :
  (l.toList = l'.toList) → (a = a' ∧ b = b' ∧ HEq l l') := by
  induction l generalizing l' a' with
  | singleton a => cases l' with
    | singleton _ => simp only [toList_singleton, List.cons.injEq, and_true] ; rintro rfl; simp
    | cons _ _ _ => simp
  | cons _ _ _ hl =>
    cases l' with
    | singleton _ => simp
    | cons _ l' _ =>
      simp only [toList_cons, List.cons.injEq, and_imp]
      rintro rfl heq
      rename_i l _ _ _
      specialize hl _ heq
      obtain ⟨rfl,rfl,hl⟩ := hl
      simp only [heq_eq_eq] at hl
      simp only [heq_eq_eq, cons.injEq, true_and]
      tauto

instance [IsEmpty α] {a b : α} : IsEmpty (a -[r]→* b) where
  false _ := IsEmpty.false a

-- doesn't work
-- instance [Inhabited α] {a b : α} : Inhabited (a -[r]→* b) where
--   default := singleton default

/-- The length of an `r`-series is defined by the number of *steps* in the series.
  This means the shortest series has *length* 0, but *one* element. -/
def length {a b : α} (l : a -[r]→* b) : ℕ := match l with
  | .singleton a => 0
  | .cons a b hab => length b + 1

@[simp]
lemma length_singleton (a : α) : (singleton (r := r) a).length = 0 := rfl

@[simp]
lemma length_cons (a : α) {b b' : α} (l : b -[r]→* b') (hab : r a b) :
  (l.cons a hab).length = l.length + 1 := rfl

lemma length_pos_of_ne {a b : α} (hne : a ≠ b) (x : a -[r]→* b) :
  0 < x.length := by
  cases x <;> simp_all

lemma length_toList {a b : α} (l : a -[r]→* b) : l.toList.length = l.length + 1 := by
  induction l <;> simp_all

/-- the coercion of an `r`-series to a function returning the value of the series at an index -/
def toFun {a b : α} (p : a -[r]→* b) : Fin (p.length + 1) → α := match p with
  | .singleton c => fun _ => c
  | .cons a l _ => fun
    | ⟨0,_⟩ => a
    | ⟨n+1,h⟩ => toFun l ⟨n,by simp_all⟩

instance {a b : α}: CoeFun (a -[r]→* b) (fun x ↦ Fin (x.length + 1) → α) :=
{ coe := RelSeriesHT.toFun}

@[simp]
lemma toFun_zero {a b : α} (p : a -[r]→* b) : p 0 = a := by
  cases p <;> rfl

@[simp]
lemma toFun_singleton (a : α) (x : Fin ((singleton (r := r) a).length + 1)) :
  (singleton a).toFun x = a := rfl

-- not quite sure how to make this simp
lemma toFun_cons_succ (a : α) {b b': α} (p : b -[r]→* b') (hab : r a b)
    (n : Fin ((cons a p hab).length)) : (cons a p hab) (n.succ) = p (n.castLT n.prop) := by
  simp only [length_cons]
  rfl

lemma toFun_length {a b : α} (p : a -[r]→* b) : p p.length = b := by
  induction p with
  | singleton a => rfl
  | cons a l hab ih => simp_all [Fin.last,toFun]

section ofLE

/--
Given two relations `r, s` on `α` such that `r ≤ s`, any relation series of `r` induces a relation
series of `s`
-/
def ofLE {a b : α} (x : a -[r]→* b) {s : Rel α α} (h : r ≤ s) : a -[s]→* b :=
  match x with
  | .singleton a => .singleton a
  | .cons a l hab => .cons a (l.ofLE h) (h _ _ hab)

@[simp]
lemma ofLE_singleton (a : α) {s : Rel α α} (h : r ≤ s) : ofLE (singleton a) h = singleton a := rfl

@[simp]
lemma ofLE_cons (a : α) {b b' : α} (l : b -[r]→* b') (hab : r a b) {s : Rel α α} (h : r ≤ s):
  ofLE (cons a l hab) h = cons a (ofLE l h) (h _ _ hab) := rfl

@[simp]
lemma head_ofLE {a b : α} (x : a -[r]→* b) {s : Rel α α} (h : r ≤ s) :
  head (ofLE x h) = a := rfl

@[simp]
lemma getLast_ofLE {a b : α} (x : a -[r]→* b) {s : Rel α α} (h : r ≤ s) :
  getLast (ofLE x h) = b := rfl


@[simp]
lemma toList_ofLe {a b : α} (x : a -[r]→* b) {s : Rel α α} (h : r ≤ s) :
    toList (ofLE x h) = toList x := by
  induction x <;> simp_all

end ofLE

section fromListChain'

/-- any nonempty `List` that satisfies `List.Chain' r` induces an `r`-series
  given by its elements -/
def fromListChain' (x : List α) (x_ne_nil : x ≠ []) (hx : x.Chain' r) :
    RelSeriesHT r (x.head x_ne_nil) (x.getLast x_ne_nil) := match x with
  | [] => (x_ne_nil rfl).elim
  | [a] => .singleton a
  | a::b::xs => .cons a (fromListChain' (b::xs) (List.cons_ne_nil b xs)
    (List.chain'_cons.mp hx).right)
    (List.chain'_cons.mp hx |>.left)

@[simp]
lemma fromListChain'_singleton (a : α) (ne_nil : [a] ≠ [] := List.cons_ne_nil a [])
    (hchain : [a].Chain' r := List.chain'_singleton a) :
    fromListChain' [a] ne_nil hchain = singleton a := rfl

@[simp]
lemma fromListChain'_cons_cons (a b : α) (l : List α)
    (cons_l_ne_nil : (b::l) ≠ [] := List.cons_ne_nil b l) (cons_l_chain' : (b::l).Chain' r)
    (hab : r a b) (hchain : (a::b::l).Chain' r := List.Chain'.cons hab cons_l_chain')
    (h_ne_nil : (a::b::l) ≠ [] := List.cons_ne_nil a (b :: l)) :
    fromListChain' (a::b::l) h_ne_nil hchain =
      cons a (fromListChain' (b::l) cons_l_ne_nil cons_l_chain') hab := rfl

@[simp]
lemma head_fromListChain' (l : List α) (l_ne_nil : l ≠ []) (hl_chain' : l.Chain' r):
  head (fromListChain' l l_ne_nil hl_chain') = l.head l_ne_nil := rfl

@[simp]
lemma getLast_fromListChain' (l : List α) (l_ne_nil : l ≠ []) (hl_chain' : l.Chain' r):
  getLast (fromListChain' l l_ne_nil hl_chain') = l.getLast l_ne_nil := rfl

@[simp]
lemma length_fromListChain' (l : List α) (ne_nil : l ≠ []) (hchain' : l.Chain' r) :
  (fromListChain' l ne_nil hchain').length + 1 = l.length := by
  induction l with
  | nil => contradiction
  | cons head tail ih =>
    cases tail with
    | nil => simp
    | cons head' tail =>
      rw [fromListChain'_cons_cons head head' tail (List.cons_ne_nil head' tail)
        (List.chain'_cons.mp hchain').right (List.chain'_cons.mp hchain').left, length_cons head,
        ih (List.cons_ne_nil _ tail)]
      rfl

@[simp]
lemma toList_fromListChain' (l : List α) (ne_nil : l ≠ []) (hchain' : l.Chain' r) :
    toList (fromListChain' l ne_nil hchain') = l := by
  fun_induction fromListChain' l ne_nil hchain' with
  | case1 => contradiction
  | case2 => simp
  | case3 a b l hl_ne_nil hl_chain ih =>
    rw [fromListChain'_cons_cons (r := r) a b l (List.cons_ne_nil b l)
      (List.chain'_cons.mp hl_chain).right (List.chain'_cons.mp hl_chain).left]
    simp_all

end fromListChain'

lemma toList_injective {a b : α} : Function.Injective (@RelSeriesHT.toList α r a b) :=
  fun _ _ h ↦ eq_of_heq (ext _ _ h).right.right

section ofRel

/-- `ofRel` gives the length 1 `r`-series induced by the relation `r a b`. -/
def ofRel {a b : α} (hr : r a b) : a -[r]→* b := .cons a (.singleton b) hr

@[simp]
lemma length_ofRel {a b : α} (hr : r a b) : length (ofRel hr) = 1 := rfl

@[simp]
lemma head_ofRel {a b : α} (hr : r a b) : head (ofRel hr) = a := rfl

@[simp]
lemma getLast_ofRel {a b : α} (hr : r a b) : getLast (ofRel hr) = b := rfl

@[simp]
lemma toList_ofRel {a b : α} (hr : r a b) : toList (ofRel hr) = [a,b] := rfl

lemma nonempty_of_rel {a b : α} (hr : r a b) : Nonempty (a -[r]→* b) :=
  ⟨ofRel hr⟩

end ofRel

section snoc

/-- `snoc` is a variation on the `cons` operation, which puts
  the extra element on the end of the series (as opposed on the head end). -/
@[match_pattern]
def snoc {a b : α} (x : a -[r]→* b) (b' : α) (hr : r b b') : a -[r]→* b' :=
  match x with
  | .singleton a => .cons a (.singleton b') hr
  | .cons a b hr' => .cons a (snoc b b' hr) hr'

@[simp]
lemma snoc_singleton (a b : α) (hr : r a b) :
  snoc (.singleton a) b hr = .cons a (.singleton b) hr := rfl

@[simp]
lemma snoc_cons (a : α) {b b' : α} (l : b -[r]→* b') (hab : r a b) (c : α) (hr : r b' c) :
  snoc (.cons a l hab) c hr = .cons a (snoc l c hr) hab := rfl

@[simp]
lemma head_snoc {a b : α} (x : a -[r]→* b) (c : α) (hr : r b c) :
  head (snoc x c hr) = a := rfl

@[simp]
lemma getLast_snoc {a b : α} (x : a -[r]→* b) (c : α) (hr : r b c) :
  getLast (snoc x c hr) = c := rfl

@[simp]
lemma toList_snoc {a b : α} (x : a -[r]→* b) (c : α) (hr : r b c) :
    toList (snoc x c hr) = (toList x) ++ [c] := by
  induction x <;> simp_all

@[simp]
lemma length_snoc {a b : α} (x : a -[r]→* b) (c : α) (hr : r  b c) :
    length (snoc x c hr) = length x + 1 := by
  induction x <;> simp_all

end snoc

section copy

/--
Change the endpoints of an `r`-series using equalities. This is useful for relaxing
definitional equality constraints, as well as allowing us to state more complicated lemmas.
simp normal form is moving the copy *outwards* , to enable computation within the "copy" context.
-/
def copy {a b a' b' : α} (x : a -[r]→* b) (ha : a = a') (hb : b = b') :
  a' -[r]→* b' := cast (ha ▸ hb ▸ rfl) x

@[simp]
lemma copy_rfl_rfl {a b : α} (x : a -[r]→* b) :
  x.copy rfl rfl = x := rfl

@[simp]
lemma cons_copy (c : α) {a b a' b' : α} (x : a -[r]→* b) (hr : r c a')
    (ha : a = a') (hb : b = b') :
    cons c (copy x ha hb) hr = copy (.cons c x (ha ▸ hr)) rfl hb := by
  cases ha; cases hb; rfl

@[simp]
lemma snoc_copy {a b a' b'} (x : a -[r]→* b) (c : α) (hr : r b' c)
    (ha : a = a') (hb : b = b') :
    snoc (copy x ha hb) c hr = copy (.snoc x c (hb ▸ hr)) ha rfl := by
  cases ha; cases hb; rfl

@[simp]
lemma toList_copy {a b a' b' : α} (x : a -[r]→* b) (ha : a = a') (hb : b = b') :
  toList (copy x ha hb) = toList x := by
  cases ha; cases hb; rfl

@[simp]
lemma length_copy {a b a' b' : α} (x : a -[r]→* b) (ha : a = a') (hb : b = b') :
    length (copy x ha hb) = length x := by
  cases ha; cases hb; rfl

end copy

section append

/--
If `a₀ -r→ a₁ -r→ ... -r→ aₙ` and `b₀ -r→ b₁ -r→ ... -r→ bₘ` are two strict series
such that `aₙ = b₀`, then there is a chain of length `n + m` given by
`a₀ -r→ a₁ -r→ ... -r→ aₙ = b₀ -r→ b₁ -r→ ... -r→ bₘ`.
-/
@[match_pattern]
def append {a b c : α} (x : a -[r]→* b) (y : b -[r]→* c) : a -[r]→* c :=
  match x with
  | .singleton a => y
  | .cons a l hl => .cons a (append l y) hl

instance {a b b' : α}: HAppend (a -[r]→* b) (b -[r]→* b') (a -[r]→* b') where
  hAppend l r := append l r

@[simp]
lemma singleton_append {a b : α} (x : a -[r]→* b) :
  (singleton (r := r) a) ++ x = x := rfl

@[simp]
lemma cons_append (a : α) {b b' c: α} (x : b -[r]→* b') (hr : r a b) (y : b' -[r]→* c) :
  (cons a x hr) ++ y = .cons a (x ++ y) hr := rfl

@[simp]
lemma append_singleton {a b : α} (x : a -[r]→* b) :
  x ++ (singleton (r := r) b) = x := by
  induction x <;> simp_all

@[simp]
lemma append_snoc {a b b' : α} (x : a -[r]→* b) (y : b -[r]→* b') (c : α)
    (hr : r b' c) :
    x ++ (snoc y c hr) = snoc (x ++ y) c hr := by
  induction x <;> simp_all

@[simp]
lemma snoc_append {a b : α} (x : a -[r]→* b) (b' : α) (hr : r b b') {c : α} (y : b' -[r]→* c):
    snoc x b' hr ++ y = x ++ cons b y hr := by
      induction x <;> simp_all

@[simp]
lemma length_append {a b b' : α} (x : a -[r]→* b) (y : b -[r]→* b') :
    length (x ++ y) = length x + length y := by
  induction x with
  | singleton a => simp
  | cons a l hab ih =>
    simp_all only [cons_append, length_cons]
    exact Nat.add_right_comm l.length y.length 1

@[simp]
lemma append_assoc {a b c d : α} (x : a -[r]→* b) (y : b -[r]→* c)
    (z : c -[r]→* d):
  (x ++ y) ++ z = x ++ (y ++ z) := by
  induction x <;> simp_all

@[simp]
lemma toList_append {a b b' : α} (x : a -[r]→* b) (y : b -[r]→* b') :
    toList (x ++ y) = toList x ++ (toList y).tail := by
  induction x with
  | singleton a =>
    simp
    cases h:y.toList with
    | nil => exact ((toList_ne_nil y) h).elim
    | cons head tail =>
      simp only [List.tail_cons, List.cons.injEq, and_true]
      change (head :: tail).head (List.cons_ne_nil head tail) = y.head
      simp_rw [← h,head_toList]
      rfl
  | cons a l hab ih => simp_all

lemma toList_append' {a b b' : α} (x : a -[r]→* b) (y : b -[r]→* b') :
    toList (x ++ y) = (toList x).dropLast ++ (toList y) := by
  induction x with
  | singleton a => simp
  | cons a l hab ih =>
    simp_all only [toList_append, cons_append, toList_cons]
    cases l <;> simp


end append


section reverse

/--
A relation series `a₀ -r→ a₁ -r→ ... -r→ aₙ` of `r` gives a relation series of the reverse of `r`
by reversing the series `aₙ ←r- aₙ₋₁ ←r- ... ←r- a₁ ←r- a₀`.
-/
def reverse {a b : α} (x : a -[r]→* b) : b -[(Function.swap r)]→* a := match x with
  | .singleton a => .singleton a
  | .cons a b hr => .snoc (reverse b) a hr

variable (r) in
@[simp]
lemma reverse_singleton (a : α) : reverse (.singleton (r := r) a) = .singleton a := rfl

@[simp]
lemma reverse_cons (a : α) {b b' : α} (x : b -[r]→* b') (hr : r a b) :
  reverse (.cons a x hr) = snoc (reverse x) a hr := rfl

@[simp]
lemma reverse_snoc {a b : α} (x : a -[r]→* b) (c : α) (hr : r b c) :
  reverse (snoc x c hr) = .cons c (reverse x) hr := by
  induction x <;> simp_all


@[simp]
lemma toList_reverse {a b : α} (x : a -[r]→* b) :
    toList (reverse x) = .reverse (toList x) := by
  induction x <;> simp_all

@[simp]
lemma reverse_copy {a b a' b' : α} (x : a -[r]→* b) (ha : a = a') (hb : b = b'):
    reverse (copy x ha hb) = copy (reverse x) hb ha := by
  cases ha; cases hb; rfl

lemma fromListChain'_reverse (l : List α) (l_ne_nil : l ≠ []) (hl_chain' : l.Chain' r) :
  fromListChain' (r := fun x y => r y x) (l.reverse) (List.reverse_ne_nil_iff.mpr l_ne_nil)
    (List.chain'_reverse.mpr hl_chain') =
      copy (reverse (fromListChain' l l_ne_nil hl_chain'))
      (List.getLast_eq_head_reverse l_ne_nil) (List.head_eq_getLast_reverse l_ne_nil) := by
  refine eq_of_heq (ext _ _ ?_).right.right
  simp

lemma reverse_fromListChain' (l : List α) (l_ne_nil : l ≠ []) (hl_chain' : l.Chain' r) :
    (fromListChain' l l_ne_nil hl_chain').reverse
      = copy (fromListChain' (l.reverse) (List.reverse_ne_nil_iff.mpr l_ne_nil)
          (List.chain'_reverse.mpr hl_chain'))
        (List.head_reverse (List.reverse_ne_nil_iff.mpr l_ne_nil)) (List.getLast_reverse _) := by
  refine eq_of_heq (ext _ _ ?_).right.right
  simp_all

@[simp]
lemma reverse_reverse {a b : α} (x : a -[r]→* b) :
  x.reverse.reverse = x := by
  induction x <;> simp_all

@[simp]
lemma reverse_append {a b c : α} (x : a -[r]→* b) (y : b -[r]→* c) :
  (x ++ y).reverse = y.reverse ++ x.reverse := by
  induction x <;> simp_all

@[simp]
lemma length_reverse {a b : α} (x : a -[r]→* b) :
  x.reverse.length = x.length := by
  induction x <;> simp_all

end reverse

section map

/--
For two preorders `α, β`, if `f : α → β` is strictly monotonic, then a strict chain of `α`
can be pushed out to a strict chain of `β` by
`a₀ < a₁ < ... < aₙ ↦ f a₀ < f a₁ < ... < f aₙ`
-/
def map {β : Type*} {s : Rel β β} (f : r →r s) {a b : α} (x : a -[r]→* b) :
    (f a) -[s]→* (f b) := match x with
  | .singleton a => .singleton (f a)
  | .cons a l hr => .cons (f a) (map f l) (f.map_rel hr)

@[simp]
lemma map_singleton {β : Type*} {s : Rel β β} (f : r →r s) (a : α) :
  map f (singleton (r := r) a) = singleton (f a) := rfl

@[simp]
lemma map_cons {β : Type*} {s : Rel β β} (f : r →r s)
  (a : α) {b b' : α} (x : b -[r]→* b') (hr : r a b) :
  map f (cons a x hr) = cons (f a) (map f x) (f.map_rel hr) := rfl

@[simp]
lemma map_snoc {β : Type*} {s : Rel β β} (f : r →r s)
    {a b : α} (x : a -[r]→* b) (c : α) (hr : r b c) :
    map f (snoc x c hr) = snoc (map f x) (f c) (f.map_rel hr) := by
  induction x <;> simp_all

@[simp]
lemma map_append {β : Type*} {s : Rel β β} (f : r →r s)
    {a b c : α} (x : a -[r]→* b) (y : b -[r]→* c) :
    map f (x ++ y) = (map f x) ++ (map f y) := by
  induction x <;> simp_all

@[simp]
lemma toList_map {β : Type*} {s : Rel β β} (f : r →r s) {a b : α} (x : a -[r]→* b) :
    toList (map f x) = (toList x).map f := by
  induction x <;> simp_all

end map

section mem

instance membership {a b : α} : Membership α (a -[r]→* b) :=
  ⟨Function.swap (· ∈ Set.range ·)⟩

variable {a b : α} {s : a -[r]→* b} {x : α}
theorem mem_def : x ∈ s ↔ x ∈ Set.range s := Iff.rfl

@[simp] theorem mem_toList : x ∈ s.toList ↔ x ∈ s := by
  rw [mem_def]
  induction s with
  | singleton a =>
    simp only [toList_singleton, List.mem_cons, List.not_mem_nil, or_false, length_singleton,
      Nat.reduceAdd, Set.mem_range, toFun_singleton, eq_comm, exists_const]
  | cons a l hab ih =>
    simp_all only [Set.mem_range, toList_cons, List.mem_cons, length_cons]
    refine ⟨(·.elim (⟨0,·.symm⟩) (·.elim (⟨·.succ,·⟩))),
      (·.elim (·.cases (.inl ·.symm) (.inr ⟨·,·⟩)))⟩

@[simp]
lemma mem_singleton_iff {a x : α} : x ∈ singleton (r := r) a ↔ x = a := by
  simp [← mem_toList]

@[simp]
lemma mem_cons_iff (c : α) (hr : r c a) : x ∈ cons c s hr ↔ x = c ∨ x ∈ s := by
  simp [← mem_toList]

@[simp]
lemma mem_snoc_iff (c : α) (hr : r b c) : x ∈ snoc s c hr ↔ x ∈ s ∨ x = c := by
  simp [← mem_toList]

@[simp]
lemma mem_append_iff {c : α} {t : b -[r]→* c} : x ∈ s ++ t ↔ x ∈ s ∨ x ∈ t := by
  simp [← mem_toList]
  refine ⟨(·.elim .inl (.inr <| List.mem_of_mem_tail ·)),(·.elim .inl ?_)⟩
  cases t with
  | singleton a =>
    simp only [toList_singleton, List.mem_cons, List.not_mem_nil, or_false, mem_toList,
      List.tail_cons]
    rintro rfl
    exact ⟨s.length,toFun_length s⟩
  | cons a l hab =>
    simp only [toList_cons, List.mem_cons, mem_toList, List.tail_cons]
    exact (·.elim (fun h => .inl (h.symm ▸ ⟨s.length,toFun_length s⟩)) .inr)

@[simp]
lemma mem_reverse_iff : x ∈ s.reverse ↔ x ∈ s := by
  simp [← mem_toList]

@[simp]
lemma head_mem : a ∈ s := ⟨0,toFun_zero s⟩

@[simp]
lemma getLast_mem : b ∈ s := ⟨s.length,toFun_length s⟩

@[simp]
lemma mem_map {β : Type*} {t : Rel β β} (f : r →r t) {y : β} : y ∈ map f s ↔ ∃ x ∈ s, f x = y := by
  simp_all [← mem_toList]

end mem
end RelSeriesHT

namespace RelSeriesHT
section LE

/--
given `x y : a -[r]→* b`, we say that `x` is less than `y` if `y` can be obtained from `x` by
substituting single steps or values in `x` for any `r`-series with the right start and end points.

For example, using (· < ·) as a relation on naturals, we have that `[0,2,3] ≤ [0,1,2,3]`
as we can substitute the `0,2` step with `[0,1,2]`.
Of note is the fact that if `r a a`, then we have `[a,a] ≤ [a]`.
-/
protected inductive le {rel : Rel α α} : {a b : α} → (l r : a -[rel]→* b) → Prop where
  | ofSingleton {a : α} (x : a -[rel]→* a) : RelSeriesHT.le (.singleton a) x
  | ofSubstCons {a b : α} (hr : rel a b) (hseries : a -[rel]→* b) {c : α} {l r : b -[rel]→* c}
    (hle : RelSeriesHT.le l r) : RelSeriesHT.le (.cons a l hr) (hseries ++ r)

section
private lemma le_refl {a b : α} (l : a -[r]→* b) : l.le l := l.rec (.ofSingleton <| .singleton ·)
  fun _ _ _ _ hr hle => le.ofSubstCons hr (ofRel hr) hle

private lemma exists_eq_append_of_append_le' {a b c : α}
  (x : a -[r]→* b) (y : b -[r]→* c) (z : a -[r]→* c) (h : (x ++ y).le z) :
    ∃ (x' : a -[r]→* b), ∃ (y' : b -[r]→* c), x' ++ y' = z ∧ x.le x' ∧ y.le y' := by
  induction x with
  | singleton a =>
    simp_all only [singleton_append]
    use (singleton a), z
    simp_all only [singleton_append, and_true, true_and]
    exact le_refl _
  | cons a l hab ih =>
    simp_all only [cons_append]
    cases h with
    | ofSubstCons hr hseries hle =>
      obtain ⟨x',y',rfl,hl,hr⟩ := ih _ _ hle
      use (hseries ++ x'), y'
      simp only [append_assoc, true_and]
      use (le.ofSubstCons _ hseries hl)

private lemma le_trans {a b : α} (x y z : a -[r]→* b) (hxy : x.le y) (hyz : y.le z) : x.le z := by
  induction hxy with
  | ofSingleton z => exact le.ofSingleton z
  | ofSubstCons hr hseries hle ih =>
    obtain ⟨x',y',rfl,hx',hy'⟩ := exists_eq_append_of_append_le' _ _ _ hyz
    cases hx' with
    | ofSingleton x =>
      simp_all
      apply le.ofSubstCons _ (singleton _) (ih _ hyz)
    | ofSubstCons hr' hseries hle =>
      simp_all
      rw [← append_assoc]
      apply le.ofSubstCons _ (hseries ++ _) (ih _ hy')

instance {a b : α} : Preorder (a -[r]→* b) where
  le := RelSeriesHT.le
  le_refl := le_refl
  le_trans := le_trans

lemma exists_eq_append_of_append_le {a b c : α}
  (x : a -[r]→* b) (y : b -[r]→* c) (z : a -[r]→* c) (h : (x ++ y) ≤ z) :
    ∃ (x' : a -[r]→* b), ∃ (y' : b -[r]→* c), x' ++ y' = z ∧ x ≤ x' ∧ y ≤ y' :=
  exists_eq_append_of_append_le' x y z h

end

@[simp]
lemma le_def {a b :α} (x y : a -[r]→* b) : x.le y ↔ x ≤ y := Iff.rfl


@[simp]
lemma singleton_le {a : α} (x : a -[r]→* a) : singleton a ≤ x := RelSeriesHT.le.ofSingleton x

lemma cons_le_append (a : α) {b c : α} (hr : r a b) (x : a -[r]→* b) {y y' : b -[r]→* c}
    (hy : y ≤ y') : cons a y hr ≤ (x ++ y') := RelSeriesHT.le.ofSubstCons hr x hy

@[elab_as_elim, induction_eliminator]
lemma le_induction {motive : {a b : α} → (x y : a -[r]→* b) → x ≤ y → Prop}
    (ofSingleton : {a : α} → (x : a-[r]→* a) → motive (singleton a) x (singleton_le x))
    (ofSubstCons : {a b : α} → (hr : r a b) → (hseries : a -[r]→* b) → {c : α} →
      {y y' : b -[r]→* c} → (hle : y ≤ y') → motive y y' hle →
      motive (cons a y hr) (hseries ++ y') (cons_le_append a hr hseries hle) )
    {a b : α}
    {x y: a -[r]→* b} (hle : x ≤ y)
     : motive x y hle :=
  @le.rec α r motive ofSingleton ofSubstCons a b x y hle

@[elab_as_elim, cases_eliminator]
lemma le_casesOn {motive : {a b : α} → (x y : a -[r]→* b) → x ≤ y → Prop}
    (ofSingleton : {a : α} → (x : a-[r]→* a) → motive (singleton a) x (singleton_le x))
    (ofSubstCons : {a b : α} → (hr : r a b) → (hseries : a -[r]→* b) → {c : α} →
      {y y' : b -[r]→* c} → (hle : y ≤ y') →
      motive (cons a y hr) (hseries ++ y') (cons_le_append a hr hseries hle) )
    {a b : α}
    {x y: a -[r]→* b} (hle : x ≤ y)
     : motive x y hle :=
  @le.casesOn α r motive a b x y hle ofSingleton @ofSubstCons

@[simp]
lemma ofRel_le {a b : α} (hr : r a b) (x : a -[r]→* b) : ofRel hr ≤ x := by
  convert cons_le_append a hr (x) (singleton_le (r := r) (singleton b))
  simp

lemma append_right_mono {a b c : α} (l : a -[r]→* b):
  Monotone (α := b -[r]→* c) (l ++ ·) := by
  intro x y
  induction l with
  | singleton a => exact id
  | cons a l hab ih =>
    intro h
    exact cons_le_append a hab (ofRel hab) (ih h)

lemma append_left_mono {a b c : α} (l : b -[r]→* c):
  Monotone (α := a -[r]→* b) (· ++ l) := by
  intro x y h
  induction h with
  | ofSingleton x =>
    simp only [singleton_append]
    induction l with
    | singleton a =>
      exact singleton_le _
    | cons a l hab ih =>
      rw [← snoc_append]
      exact cons_le_append _ _ _ (le_refl _)
  | ofSubstCons hr hseries hle ih =>
    simp_all
    exact cons_le_append _ hr hseries (ih l)

@[simp]
lemma snoc_le_append {a b : α} {x x' : a -[r]→* b}
    (hy : x ≤ x') (c : α) (hr : r b c) (y : b -[r]→* c): snoc x c hr ≤ (x' ++ y) := by
  induction x with
  | singleton a =>
    convert cons_le_append _ hr (x' ++ y) (singleton_le (singleton c)) using 1
    simp
  | cons a l hab ih =>
    simp only [snoc_cons]
    cases hy with
    | ofSubstCons hr' hseries hle' =>
      rw [append_assoc]
      convert cons_le_append a hab (hseries) (ih hle' hr y)

lemma reverse_mono {a b : α} : Monotone (α := a -[r]→* b) (·.reverse) := by
  intro x y hxy
  simp only
  induction hxy with
  | ofSingleton a => simp
  | ofSubstCons hr hseries hle hi => simp_all

def reverse_gi {a b : α} : GaloisInsertion (α := a -[r]→* b) (·.reverse) (·.reverse) where
  choice x _ := x.reverse
  gc := by
    rw [GaloisConnection]
    intro x y
    constructor
    · rw [← reverse_reverse y]
      nth_rw 2 [← reverse_reverse x]
      apply reverse_mono
    · nth_rw 2 [← reverse_reverse y]
      apply reverse_mono
  le_l_u := by intros;simp
  choice_eq _ _ := rfl

def reverse_gci {a b : α} : GaloisCoinsertion (α := a -[r]→* b) (·.reverse) (·.reverse) where
  choice x _ := x.reverse
  gc := by
    rw [GaloisConnection]
    intro x y
    constructor
    · rw [← reverse_reverse y]
      nth_rw 2 [← reverse_reverse x]
      apply reverse_mono
    · nth_rw 2 [← reverse_reverse y]
      apply reverse_mono
  u_l_le := by intros; simp
  choice_eq _ _ := rfl

lemma reverse_strictMono {a b : α} : StrictMono (α := a -[r]→* b) (·.reverse) := by
  intro x y hxy
  simp only
  have hle := reverse_mono hxy.le
  use hle
  contrapose hxy
  simp only [le_def, not_not,not_lt_iff_le_imp_le] at hxy ⊢
  rw [← reverse_reverse x, ← reverse_reverse y]
  exact fun _ => reverse_mono hxy
-- #check List.Sublist

lemma le_of_toList_sublist_toList {a b : α} (x y : a -[r]→* b)
    (hxy : x.toList.Sublist y.toList) : x ≤ y := by
  induction x with
  | singleton a => simp
  | cons a l hab ih =>
    simp_all
    obtain ⟨r1,r2,hy,hmem,hsub⟩ := List.cons_sublist_iff.mp hxy
    sorry


end LE

end RelSeriesHT
