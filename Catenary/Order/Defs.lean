import Catenary.RelSeriesHT.Codim
open scoped RelSeriesHT
abbrev IsCatenaryOrder (α : Type*) [Preorder α] : Prop := Rel.IsCatenary (LT.lt : Rel α α)

abbrev IsDiscreteOrder (α : Type*) [Preorder α] : Prop := Rel.IsDiscrete (LT.lt : Rel α α)

noncomputable def eCodim {α : Type*} [Preorder α] (a b : α) : WithBot ℕ∞ := Rel.eCodim LT.lt a b

lemma lt_of_relSeriesHT {α : Type*} [Preorder α] {a b : α} (h : a ≠ b) : a -[LT.lt]→* b → a < b
    | RelSeriesHT.singleton a => by
        contradiction
    | RelSeriesHT.cons a (b := c) l altc => by
        apply lt_trans altc
        match l with
        | RelSeriesHT.singleton b => exfalso; sorry -- why does this not give me the hypothesis that l is a singleton?
        | RelSeriesHT.cons c l h => sorry -- why does this keep making new variables????

        -- exact lt_of_relSeriesHT sorry l

lemma isSingleton_if {α : Type*}{a : α}[Preorder α](x : a -[(·<·)]→* a ): x = RelSeriesHT.singleton a := by
  match x with
  | RelSeriesHT.singleton a => rfl
  | RelSeriesHT.cons (b:=b) a l h =>
    simp at h
    simp only [reduceCtorEq]
    have h₁: b ≠ a := by
      intro h₂
      rw[h₂] at h
      apply lt_irrefl at h
      exact h
    have := lt_of_relSeriesHT h₁ l
    exact absurd h (lt_asymm this)

lemma isCatenaryOrder_iff_isDiscreteOrder_and_dimension_formula (α : Type*) [P: Preorder α]: IsCatenaryOrder α ↔ IsDiscreteOrder α ∧
    ∀ {a b c: α }, (a < b) → (b < c) →  eCodim a b + eCodim b c = eCodim a c := by
  unfold IsCatenaryOrder
  rw[RelSeriesHT.isCatenary_iff_isDiscrete_and_dimension_formula]
  unfold IsDiscreteOrder
  simp only [and_congr_right_iff]
  intro hd
  constructor
  · intro h
    intro a b c hab hbc
    unfold eCodim
    apply h
    exact RelSeriesHT.ofRel hab
    exact RelSeriesHT.ofRel hbc
  · intro h'
    intro a b c h'ab h'bc
    by_cases he₁ : a = b
    · by_cases he₂ : b = c
      · rw[he₁, he₂] at h'ab
        rw[he₂] at h'bc
        rw[he₁, he₂]
        have h'': Rel.eCodim LT.lt c c = 0 := by
          sorry
        rw[h'']
        rfl
      · rw[he₁]
        have h'': Rel.eCodim LT.lt b b = 0 := by
          sorry
        rw[h'']
        rw[zero_add]
    · by_cases he₃ : b = c
      · rw[he₃]
        have h'': Rel.eCodim LT.lt c c = 0 := by
          sorry
        rw[h'']
        rw[add_zero]
      · apply h'
        apply lt_of_relSeriesHT
        push_neg at he₁
        exact he₁
        exact h'ab
        apply lt_of_relSeriesHT
        push_neg at he₃
        exact he₃
        exact h'bc
