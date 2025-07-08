import Catenary.RelSeriesHT.Codim
open scoped RelSeriesHT
abbrev  IsCatenaryOrder (α : Type*) [Preorder α] : Prop := Rel.IsCatenary (LT.lt : Rel α α)

abbrev IsDiscreteOrder (α : Type*) [Preorder α] : Prop := Rel.IsDiscrete (LT.lt : Rel α α)

noncomputable def eCodim {α : Type*} [Preorder α] (a b : α) : WithBot ℕ∞ := Rel.eCodim LT.lt a b

lemma lt_of_relSeriesHT {α : Type*} [Preorder α] {a b : α} (h : a ≠ b) : a -[LT.lt]→* b → a < b
  | RelSeriesHT.singleton a => by
    contradiction
    | RelSeriesHT.cons a (b := c) l altc => by
      by_cases hcb : c = b
      · subst hcb
        exact altc
      · apply lt_trans altc
        exact lt_of_relSeriesHT hcb l

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
          unfold Rel.eCodim
          have h₃: ∀ x: c -[LT.lt]→* c, x.reduce.length = 0 := by
            intro x
            have h₆ : x = RelSeriesHT.singleton c := isSingleton_if x
            have h₄: x.reduce.length = 0 := by
              rw[h₆]
              simp only [RelSeriesHT.reduce_singleton, RelSeriesHT.length_singleton]
            rw[h₄]
          have h''': h'ab.reduce.length = 0 := by
            have h₅ : h'ab = RelSeriesHT.singleton c := isSingleton_if h'ab
            have h₇: h'ab.reduce.length = 0 := by
              rw[h₅]
              simp only [RelSeriesHT.reduce_singleton, RelSeriesHT.length_singleton]
            exact h₇
          apply le_antisymm
          · simp only [iSup_le_iff, Nat.cast_nonpos]
            apply h₃
          · have h₈ : (↑h'ab.reduce.length : WithBot ℕ∞) = 0 := by
              rw [h''', Nat.cast_zero]
            rw[← h₈]
            exact le_iSup_iff.mpr fun b a ↦ a h'ab
        rw[h'']
        rfl
      · rw[he₁]
        rw[he₁] at h'ab
        have h'': Rel.eCodim LT.lt b b = 0 := by
          unfold Rel.eCodim
          have h₃: ∀ x: b -[LT.lt]→* b, x.reduce.length = 0 := by
            intro x
            have h₆ : x = RelSeriesHT.singleton b := isSingleton_if x
            have h₄: x.reduce.length = 0 := by
              rw[h₆]
              simp only [RelSeriesHT.reduce_singleton, RelSeriesHT.length_singleton]
            rw[h₄]
          have h''': h'ab.reduce.length = 0 := by
            have h₅ : h'ab = RelSeriesHT.singleton b := isSingleton_if h'ab
            have h₇: h'ab.reduce.length = 0 := by
              rw[h₅]
              simp only [RelSeriesHT.reduce_singleton, RelSeriesHT.length_singleton]
            exact h₇
          apply le_antisymm
          · simp only [iSup_le_iff, Nat.cast_nonpos]
            apply h₃
          · have h₈ : (↑h'ab.reduce.length : WithBot ℕ∞) = 0 := by
              rw [h''', Nat.cast_zero]
            rw[← h₈]
            exact le_iSup_iff.mpr fun b a ↦ a h'ab
        rw[h'']
        rw[zero_add]
    · by_cases he₃ : b = c
      · rw[he₃]
        rw[he₃] at h'bc
        have h'': Rel.eCodim LT.lt c c = 0 := by
          unfold Rel.eCodim
          have h₃: ∀ x: c -[LT.lt]→* c, x.reduce.length = 0 := by
            intro x
            have h₆ : x = RelSeriesHT.singleton c := isSingleton_if x
            have h₄: x.reduce.length = 0 := by
              rw[h₆]
              simp only [RelSeriesHT.reduce_singleton, RelSeriesHT.length_singleton]
            rw[h₄]
          have h''': h'bc.reduce.length = 0 := by
            have h₅ : h'bc = RelSeriesHT.singleton c := isSingleton_if h'bc
            have h₇: h'bc.reduce.length = 0 := by
              rw[h₅]
              simp only [RelSeriesHT.reduce_singleton, RelSeriesHT.length_singleton]
            exact h₇
          apply le_antisymm
          · simp only [iSup_le_iff, Nat.cast_nonpos]
            apply h₃
          · have h₈ : (↑h'bc.reduce.length : WithBot ℕ∞) = 0 := by
              rw [h''', Nat.cast_zero]
            rw[← h₈]
            exact le_iSup_iff.mpr fun b a ↦ a h'bc
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
