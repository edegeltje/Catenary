import Catenary.RelSeriesHT.Codim

variable {α : Type*} (r : Rel α α)
open RelSeriesHT

/-- A function to the integers is a dimension function when it is (strict-) monotone and "leaves no gaps" with respect to a relation. -/
@[mk_iff]
structure Function.IsDimensionFunction (f : α → ℤ) : Prop where
  mono (a b : α) (hab : r a b) : f a ≤ f b
  strictMono (a b : α) (hab : r a b) (h : (ofRel hab).IsReduced) : f a < f b
  map_succ (a b : α) (hr : r a b) (hsucc : Maximal (·.IsReduced) (ofRel hr)) :
    f a + 1 = f b

variable {r} {f : α → ℤ}

def Function.IsDimensionFunction.toRelHom (hf : f.IsDimensionFunction r) : r →r (· ≤ · : ℤ → ℤ → Prop) where
  toFun := f
  map_rel' := hf.mono _ _

@[simp]
lemma Function.IsDimensionFunction.toRelHom_apply (hf : f.IsDimensionFunction r) (a : α) :
  hf.toRelHom a = f a := rfl

/-- move to defs -/
lemma rel_of_isTrans [IsRefl α r] [IsTrans α r] {a b : α} : a -[r]→* b → r a b := by
  intro x
  induction x with
  | singleton a => exact refl _
  | cons a l hab ih =>
    exact _root_.trans hab ih

lemma diff_nonneg {a b : α} (hf : f.IsDimensionFunction r): a -[r]→* b → 0 ≤ f b - f a := by
  simp only [Int.sub_nonneg]
  exact (rel_of_isTrans <| ·.map hf.toRelHom)

lemma eCodim_le_diff (hf : f.IsDimensionFunction r) {a b : α} : Rel.eCodim r a b ≤ (f b - f a).toNat := by
  rw [eCodim_le_nat_iff]
  intro x
  wlog hx : x.IsReduced generalizing x
  · specialize this x.reduce (reduce_isReduced x)
    rwa [← reduce_eq_self_of_isReduced _ (reduce_isReduced x)]
  rw [reduce_eq_self_of_isReduced _ hx]
  induction x with
  | singleton a => simp only [length_singleton, sub_self, Int.toNat_zero, le_refl]
  | cons a l hab ih =>
    rename_i b c
    simp_all
    have : 0 < f b - f a := by
      rw [lt_sub_iff_add_lt, zero_add]
      apply hf.strictMono _ _ hab
      simp only [IsReduced_ofRel, ne_eq]
      exact hx.left
    suffices l.length + 1 ≤ (f c - f b).toNat + (f b - f a).toNat by
      rw [← Int.toNat_add (diff_nonneg hf l) (Int.le_of_lt ‹_›)] at this
      simpa
    omega

lemma length_eq_diff_of_maximal (hf : f.IsDimensionFunction r) {a b : α} (x : a -[r]→* b) (hx : Maximal (·.IsReduced) x):
    x.length = (f b - f a).toNat := by
  induction x with
  | singleton a => simp
  | cons a l hab ih =>
    rename_i b c
    simp_all only [length_cons]
    change Maximal (·.IsReduced) (ofRel hab ++ l) at hx
    rw [← maximal_append] at hx
    rw [ih hx.right]
    suffices (f c - f b).toNat + 1 = (f c - f b).toNat + (f b - f a).toNat by
      rw [← Int.toNat_add (diff_nonneg hf l) (diff_nonneg hf (ofRel hab))] at this
      simpa
    nth_rw 3 [← hf.map_succ a b hab hx.left]
    simp

lemma Function.IsDimensionFunction.isDiscrete (hf : f.IsDimensionFunction r) : r.IsDiscrete := by
  rw [isDiscrete_iff_forall_eCodim_lt_top]
  intro a b
  apply lt_of_le_of_lt
  · exact eCodim_le_diff hf
  · exact compareOfLessAndEq_eq_lt.mp rfl

lemma diff_eq_eCodim (hf : f.IsDimensionFunction r) {a b : α} : a -[r]→* b → (f b - f a).toNat = Rel.eCodim r a b := by
  have := hf.isDiscrete
  intro x
  rw [← length_longestBetween_eq_eCodim (bot_lt_eCodim_iff.mpr ⟨x⟩) (eCodim_lt_top _ _)]
  rw [length_eq_diff_of_maximal hf]
  exact maximal_longestBetween (bot_lt_eCodim_iff.mpr (Nonempty.intro x)) (eCodim_lt_top a b)

lemma Function.IsDimensionFunction.isCatenary {f : α → ℤ} (hf : f.IsDimensionFunction r) : r.IsCatenary := by
  rw [isCatenary_iff_isDiscrete_and_dimension_formula]
  use hf.isDiscrete
  intro a b c xl xr
  rw [← diff_eq_eCodim hf xl,← diff_eq_eCodim hf xr, ← diff_eq_eCodim hf (xl ++ xr)]
  norm_cast
  rw [← Int.toNat_add (diff_nonneg hf xl) (diff_nonneg hf xr)]
  simp

-- section
-- variable (r) in
-- def ZigZag (a b : α) : Type _ := (c : α) × ({x:a -[r]→* c // Maximal (·.IsReduced) x} × {y:b -[r]→* c // Maximal (·.IsReduced) y})
-- -- def IsSucc (x y : α) : Prop := ∃ h : r x y, Maximal (·.IsReduced) (ofRel h)

-- def ZigZag.out (a b : α) : ZigZag r a b ≃ (c : α) × ({x:a -[r]→* c // Maximal (·.IsReduced) x} × {y:b -[r]→* c // Maximal (·.IsReduced) y}) := Equiv.refl _

-- variable (r) in
-- abbrev SeriesConnection (a b : α) : Type _ := a -[ZigZag r]→* b

-- def SeriesConnection.symm {a b : α} (c : SeriesConnection r a b) : SeriesConnection r b a :=
--   c.reverse.ofLE (·.map id (fun _ => Prod.swap))

-- def SeriesConnection.toInt {a b : α} (c: SeriesConnection r a b) : ℤ := match c with
--   | .singleton a => 0
--   | .cons _ l (⟨c,h⟩) => SeriesConnection.toInt l + h.fst.val.length - h.snd.val.length

-- variable (r) in
-- /-- two points are seriesconnected when there exists a composition of series either way
--   connecting them -/
-- def seriesConnected : Setoid α where
--   r a b := Nonempty (SeriesConnection r a b)
--   iseqv := by
--     constructor
--     · exact (⟨.singleton ·⟩)
--     · intro a b ⟨x⟩
--       exact ⟨x.symm⟩
--     · intro a b c ⟨x⟩ ⟨y⟩
--       exact ⟨x ++ y⟩

-- variable (r) in
-- lemma quot_out_connected_self (a : α) : seriesConnected r (Quotient.mk (seriesConnected r) a).out a:= by
--   rw [← Quotient.eq'']
--   simp

-- noncomputable def chosen_dimensionFunction (a : α) : ℤ :=
--     (Classical.choice (quot_out_connected_self r a)).toInt

-- /- this is the hard direction: there exists a dimension function when a space is catenary -/
-- lemma exists_isDimensionFunction [r.IsCatenary] : ∃ g : α → ℤ, g.IsDimensionFunction r := by
--   rename_i inst
--   rw [Rel.isCatenary_iff] at inst
--   revert inst
--   simp_rw [Function.isDimensionFunction_iff]
--   contrapose!
--   simp_all only [IsReduced_ofRel, ne_eq, exists_and_right]
--   intro h

--   sorry


-- end
