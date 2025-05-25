import Catenary.RelSeriesHT.Codim

open RelSeriesHT
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

lemma isCatenaryOrder_iff_isDiscreteOrder_and_dimension_formula (α : Type*) [Preorder α]: IsCatenaryOrder α ↔ IsDiscreteOrder α ∧
    ∀ {a b c: α }, a < b → b < c →  eCodim a b + eCodim b c = eCodim a c := sorry
