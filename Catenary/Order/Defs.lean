import Catenary.RelSeriesHT.Codim
open scoped RelSeriesHT
abbrev IsCatenaryOrder (α : Type*) [Preorder α] : Prop := Rel.IsCatenary (LT.lt : Rel α α)

abbrev IsDiscreteOrder (α : Type*) [Preorder α] : Prop := Rel.IsDiscrete (LT.lt : Rel α α)

noncomputable def eCodim {α : Type*} [Preorder α] (a b : α) : WithBot ℕ∞ := Rel.eCodim LT.lt a b

lemma isCatenaryOrder_iff_isDiscreteOrder_and_dimension_formula (α : Type*) [Preorder α]: IsCatenaryOrder α ↔ IsDiscreteOrder α ∧
    ∀ {a b c: α }, a < b → b < c →  eCodim a b + eCodim b c = eCodim a c := sorry
