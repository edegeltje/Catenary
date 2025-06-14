import Catenary.RelSeriesHT.Defs
import Mathlib.Data.ENat.Lattice
import Mathlib.Order.Minimal

variable {α : Type*} {r : Rel α α}

namespace Rel
/-
Of note in this section, we don't assume the existance of `r`-series between all pairs of points.
Instead we assume that *if any exist*, the relevant property holds.
This allows the notions to (mostly) coincide with those for transitive orders.
-/
open scoped RelSeriesHT

/-- A relation `r` is said to be dense iff for every two points `a` and `b` and a `r`-series
  between them, there is another r-series which is strictly larger. For transitive `· < ·`,
  equivalent to DenselyOrdered. -/
@[mk_iff]
class IsDense (r : Rel α α) : Prop where
  /-- A relation `r` is said to be dense iff for every two points `a` and `b` and a `r`-series
    between them, there is another r-series which is strictly larger. For transitive `· < ·`,
    equivalent to DenselyOrdered. -/
  isDense (r) (a b : α) : ∀ (x : a -[r]→* b), ∃ (y : a -[r]→* b),
    x < y

/-- A relation `r` is said to be discrete iff for all points `a`, `b`,
  there is length of `r`-series such that every series is less than a `r`-series of such length -/
@[mk_iff]
class IsDiscrete (r : Rel α α) : Prop where
  /-- A relation `r` is said to be discrete iff for all points `a`, `b`,
    every `r`-series essentially has a maximum length -/
  isDiscrete (r) (a b : α) : ∃ n, ∀ (x : a -[r]→* b), ∃ (y : a -[r]→* b),
    y.IsReduced ∧ x ≤ y ∧ y.length ≤ n

/-- A relation `r` is said to be catenary iff for every two points `a` and `b`,
  any `r`-series extends to a reduced `r`-series of length `n`. -/
@[mk_iff]
class IsCatenary (r : Rel α α) : Prop where
  /-- A relation `r` is said to be catenary iff for every two points `a` and `b`,
    any `r`-series extends to a reduced `r`-series of length `n`. -/
  isCatenary (r) (a b : α) : ∃ n, ∀ (x : a -[r]→* b),
    ∃ (y : a -[r]→* b), y.IsReduced ∧ x ≤ y ∧ y.length = n

end Rel

namespace RelSeriesHT

section ecodim

variable (r) in
/-- The (relative) codimension of two elements is supremum of lengths of reduced paths.
  It is -∞ when there are no paths between the two elements, and ∞ when there are arbitrarily long reduced paths. -/
noncomputable def _root_.Rel.eCodim (a b : α) : WithBot ℕ∞ := ⨆ (x : a -[r]→* b), (x.reduce.length : WithBot ℕ∞)

lemma eCodim_def (a b : α) : Rel.eCodim r a b = ⨆ (x : a -[r]→* b), (x.reduce.length : WithBot ℕ∞) := rfl

lemma length_le_eCodim_of_isReduced {a b : α} {x : a -[r]→* b} (hx : x.IsReduced) :
    x.length ≤ Rel.eCodim r a b := by
  rw [← reduce_eq_self_of_isReduced x hx, eCodim_def]
  exact le_iSup_iff.mpr fun b_1 a ↦ a x

lemma eCodim_eq_bot_iff {a b : α} : Rel.eCodim r a b = ⊥ ↔ IsEmpty (a -[r]→* b) := by
  simp only [eCodim_def, iSup_eq_bot, WithBot.natCast_ne_bot, isEmpty_iff]

lemma eCodim_nonneg_iff {a b : α} : 0 ≤ Rel.eCodim r a b ↔ Nonempty (a -[r]→* b) := by
  constructor
  · contrapose!
    intro h
    simp_all only [eCodim_def, not_nonempty_iff, ciSup_of_empty]
    decide
  · intro ⟨y⟩
    trans (y.reduce.length : WithBot ℕ∞)
    · simp
    · exact length_le_eCodim_of_isReduced (reduce_isReduced y)

lemma bot_lt_eCodim_iff {a b : α} : ⊥ < Rel.eCodim r a b ↔ Nonempty (a -[r]→* b) := by
  rw [← eCodim_nonneg_iff]
  generalize Rel.eCodim r a b = z
  cases z <;> simp

lemma eCodim_eq_sSup_length_reduce (a b : α) :
    Rel.eCodim r a b = ⨅ (n : WithBot ℕ∞), ⨅ (_ : ∀ (x : a -[r]→* b), ∃ y, x ≤ y ∧ y.length ≤ n), (n : WithBot ℕ∞):= by
  rw [eCodim_def]
  apply le_antisymm
  · simp_rw [le_iInf_iff,iSup_le_iff]
    intro d hd i
    obtain ⟨z,hz⟩ := hd i.reduce
    trans (z.length : WithBot ℕ∞)
    · simp only [Nat.cast_le]
      apply (reduce_isReduced i).isReduced _ hz.left
    · exact hz.right
  · simp_rw [iInf_le_iff, le_iSup_iff]
    intro d hd e he
    specialize hd e
    simp_rw [le_iInf_iff] at hd
    apply hd
    intro i
    use i.reduce, self_le_reduce i, (he i)

lemma eCodim_lt_top [inst:r.IsDiscrete] (a b : α) : Rel.eCodim r a b < ⊤ := by
  rw [eCodim_def]
  rw [iSup_lt_iff]
  obtain ⟨z,hz⟩ := inst.isDiscrete a b
  use z
  rw [← WithBot.coe_top,← WithBot.coe_natCast z, WithBot.coe_lt_coe]
  simp only [ENat.coe_lt_top, true_and]
  intro i
  obtain ⟨y,hyr,hiy,hyl⟩ := hz i
  rw [← WithBot.coe_natCast i.reduce.length,WithBot.coe_le_coe, Nat.cast_le]
  trans y.length
  · apply (reduce_isReduced i).isReduced
    apply le_trans (reduce_le_self i) hiy
  exact hyl

lemma isDiscrete_iff_forall_eCodim_lt_top : r.IsDiscrete ↔ ∀ a b, Rel.eCodim r a b < ⊤ := by
  refine ⟨@eCodim_lt_top _ _,?_⟩
  rw [Rel.isDiscrete_iff]
  intro h a b
  specialize h a b
  use (Rel.eCodim r a b).unbotD 0|>.toNat
  intro x
  have : Rel.eCodim r a b ≠ ⊥ := (bot_lt_eCodim_iff.mpr ⟨x⟩).ne.symm
  use x.reduce, reduce_isReduced x, self_le_reduce x
  rw [(WithBot.unbotD_eq_iff (y := (Rel.eCodim r a b).unbot this)).mpr (.inl
    ((WithBot.unbot_eq_iff this).mp rfl))]
  rw [← ENat.toNat_coe x.reduce.length]
  apply ENat.toNat_le_toNat _ (by
    rw [ne_eq,← (WithBot.coe_inj (a := (Rel.eCodim r a b).unbot this) (b := ⊤))]
    simp only [WithBot.coe_unbot, WithBot.coe_top]
    exact h.ne)
  · rw [← WithBot.coe_le_coe]
    simp only [WithBot.coe_unbot, WithBot.coe_natCast]
    exact length_le_eCodim_of_isReduced (reduce_isReduced x)



@[simp]
lemma reduce_length_le_eCodim {a b : α} (x : a -[r]→* b) : x.reduce.length ≤ Rel.eCodim r a b := by
  rw [eCodim_def]
  exact le_iSup_iff.mpr fun b_1 a ↦ a x

lemma eCodim_le_enat_iff {a b : α} (n : ℕ∞) : Rel.eCodim r a b ≤ n ↔
    ∀ (x : a -[r]→* b), x.reduce.length ≤ n := by
  rw [eCodim_def, iSup_le_iff]
  simp_rw [← WithBot.coe_natCast, WithBot.coe_le_coe]

lemma eCodim_le_nat_iff {a b : α} (n : ℕ) : Rel.eCodim r a b ≤ n ↔
    ∀ (x : a -[r]→* b), x.reduce.length ≤ n := by
  simp_rw [eCodim_def, iSup_le_iff,Nat.cast_le]

lemma eCodim_eq_top [r.IsDense] (a b : α) : Rel.eCodim r a b = ⊤ ↔ Nonempty (a -[r]→* b) := by
  have := ‹r.IsDense›.isDense a b
  constructor
  · rw [eCodim_eq_sSup_length_reduce]
    contrapose!
    intro h
    simp_all only [not_nonempty_iff, IsEmpty.exists_iff, IsEmpty.forall_iff, iInf_pos, ne_eq,
      iInf_eq_top, not_forall]
    use ⊥
    simp only [bot_ne_top, not_false_eq_true]
  · intro ⟨x⟩
    rw [eCodim_def]
    refine iSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_
    · simp
    · intro n
      cases n with
      | bot =>
        simp only [bot_lt_top, forall_const]
        use x
        exact WithBot.bot_lt_coe _
      | coe a =>
        cases a with
        | top => simp
        | coe a =>
          intro h
          clear h
          induction a with
          | zero =>
            obtain ⟨z,hz⟩ := this (x.reduce)
            use z.reduce
            apply lt_of_le_of_lt (b := (x.reduce.length : WithBot ℕ∞))
            · simp only [Nat.cast_zero, WithBot.coe_zero, Nat.cast_nonneg']
            · simp only [Nat.cast_lt]
              apply length_strictMono_of_isReduced (reduce_isReduced x)
              simp only [reduce_reduce]
              exact lt_of_lt_of_le hz (self_le_reduce z)
          | succ n ih =>
            obtain ⟨z,hz⟩ := ih
            obtain ⟨z',hz'⟩ := this z.reduce
            use z'
            rw [← WithBot.coe_natCast z'.reduce.length,WithBot.coe_lt_coe, Nat.cast_lt]
            rw [← WithBot.coe_natCast z.reduce.length,WithBot.coe_lt_coe, Nat.cast_lt] at hz
            have : z.reduce.length < z'.reduce.length := by
              apply length_strictMono_of_isReduced (reduce_isReduced z)
              exact lt_of_lt_of_le hz' (self_le_reduce _)
            omega

lemma eCodim_eq_one_of_maximal_ofRel {a b : α} (hr : r a b): Maximal (·.IsReduced) (ofRel hr) →
    Rel.eCodim r a b = 1 := by
  intro h
  refine iSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_
  · intro i
    have := h.right (reduce_isReduced i) (ofRel_le _ _)
    have := (reduce_isReduced i).isReduced (ofRel hr) this
    simpa
  · intro w hw
    use ofRel hr
    rw [reduce_eq_self_of_isReduced _ h.left]
    exact hw


end ecodim

section isDiscrete

section longest
lemma exists_longest_iff_bot_lt_codim_lt_top (a b : α) : (⊥ < Rel.eCodim r a b) ∧ (Rel.eCodim r a b < ⊤) ↔
    ∃ z: a -[r]→* b, z.IsReduced ∧ ∀ y : a -[r]→* b, y.IsReduced → y.length ≤ z.length := by
  constructor
  · rintro ⟨hbot,htop⟩
    have : Nonempty (a -[r]→* b) := by
      rw [eCodim_def] at hbot
      rw [bot_lt_iSup] at hbot
      exact nonempty_of_exists hbot
    rw [eCodim_def] at htop
    simp_rw [← WithBot.coe_natCast, ← WithBot.coe_top, ← WithBot.coe_iSup (OrderTop.bddAbove _),
      WithBot.coe_lt_coe] at htop
    obtain ⟨z,hz⟩ := ENat.exists_eq_iSup_of_lt_top htop
    use z.reduce,reduce_isReduced z
    intro y hy
    rw [← ENat.coe_le_coe, hz, ← reduce_eq_self_of_isReduced y hy]
    exact le_iSup_iff.mpr fun b_1 a ↦ a y
  · rintro ⟨z,hz,hz'⟩
    simp_rw [eCodim_def]
    constructor
    · simp only [bot_lt_iSup]
      use z
      exact WithBot.bot_lt_coe _
    · apply lt_of_le_of_lt (b := (z.length : WithBot ℕ∞))
      · simp only [iSup_le_iff, Nat.cast_le]
        intro i
        exact hz' i.reduce (reduce_isReduced i)
      · rw [← WithBot.coe_top,← WithBot.coe_natCast,WithBot.coe_lt_coe]
        simp

lemma isDiscrete_iff_exists_longest_of_nonempty : r.IsDiscrete ↔ ∀ a b,
    Nonempty (a -[r]→* b) →
      ∃ z: a -[r]→* b, z.IsReduced ∧ ∀ y : a -[r]→* b, y.IsReduced → y.length ≤ z.length := by
  constructor
  · intro h a b hz
    simp_rw [← exists_longest_iff_bot_lt_codim_lt_top (r := r)]
    constructor
    · exact bot_lt_eCodim_iff.mpr hz
    · exact eCodim_lt_top a b
  · intro h
    constructor
    intro a b
    specialize h a b
    contrapose! h
    constructor
    · exact nonempty_of_exists (h 0)
    intro z hz
    obtain ⟨y,hy⟩ := h z.length
    use y.reduce, reduce_isReduced y
    exact hy y.reduce (reduce_isReduced y) (self_le_reduce y)
end longest

section maximal

lemma exists_maximal_ge_of_eCodim_lt_top {a b : α} : (Rel.eCodim r a b < ⊤) →
    ∀ x: a-[r]→* b, ∃ z: a-[r]→* b, x ≤ z ∧ Maximal (·.IsReduced) z := by
  intro hdim x
  contrapose! hdim
  have _ : Nonempty (a -[r]→* b) := ⟨x⟩
  simp only [top_le_iff, eCodim_def]
  simp_rw [← WithBot.coe_natCast,← WithBot.coe_iSup (OrderTop.bddAbove _)]
  simp only [WithBot.coe_eq_top]
  refine ENat.iSup_coe_eq_top.mpr ?_
  rw [bddAbove_def]
  push_neg
  intro n
  simp only [Set.mem_range, exists_exists_eq_and]
  suffices ∃ y, x ≤ y ∧ n < y.reduce.length from this.elim (⟨·,·.right⟩)
  induction n with
  | zero =>
    specialize hdim x.reduce (self_le_reduce x)
    rw [not_maximal_iff_exists_gt (reduce_isReduced x)] at hdim
    obtain ⟨y,hy⟩ := hdim
    use y, (self_le_reduce x).trans hy.left.le
    rw [reduce_eq_self_of_isReduced _ hy.right]
    apply lt_of_le_of_lt (zero_le x.reduce.length)
    exact length_strictMono_of_isReduced (reduce_isReduced x) _ hy.left
  | succ n ih =>
    obtain ⟨x',hxx',hn⟩ := ih
    specialize hdim x'.reduce (hxx'.trans (self_le_reduce x'))
    rw [not_maximal_iff_exists_gt (reduce_isReduced x')] at hdim
    obtain ⟨y',hy'⟩ := hdim
    use y',hxx'.trans ((self_le_reduce x').trans hy'.left.le)
    rw [reduce_eq_self_of_isReduced _ hy'.right]
    have := length_strictMono_of_isReduced (reduce_isReduced x') _ hy'.left
    omega

/-- chooses a series larger than the given element which cannot be (nontrivially) extended -/
noncomputable def maximalExtension {a b : α} (hcodim : Rel.eCodim r a b < ⊤) (x : a -[r]→* b) :
  a -[r]→* b := (exists_maximal_ge_of_eCodim_lt_top hcodim x).choose

lemma maximal_maximalExtension {a b : α} (hcodim : Rel.eCodim r a b < ⊤) (x : a -[r]→* b) :
  Maximal (·.IsReduced) (maximalExtension hcodim x) := (exists_maximal_ge_of_eCodim_lt_top hcodim x).choose_spec.right

lemma self_le_maximalExtension {a b : α} (hcodim : Rel.eCodim r a b < ⊤) (x : a -[r]→* b) :
  x ≤ maximalExtension hcodim x := (exists_maximal_ge_of_eCodim_lt_top hcodim x).choose_spec.left

end maximal


end isDiscrete

section longestBetween

variable (r) in
/-- chooses a (reduced) series between the given elements of maximal length -/
noncomputable def longestBetween (a b : α) (hbot : ⊥ < Rel.eCodim r a b) (htop : Rel.eCodim r a b < ⊤) : a -[r]→* b :=
  (exists_longest_iff_bot_lt_codim_lt_top a b).mp ⟨hbot,htop⟩ |>.choose

@[simp]
lemma longestBetween_isReduced {a b : α} (hbot : ⊥ < Rel.eCodim r a b) (htop : Rel.eCodim r a b < ⊤) :
  (longestBetween r a b hbot htop).IsReduced :=
  (exists_longest_iff_bot_lt_codim_lt_top a b).mp ⟨hbot,htop⟩ |>.choose_spec.left

lemma longestBetween_longest {a b : α} (hbot : ⊥ < Rel.eCodim r a b) (htop : Rel.eCodim r a b < ⊤) :
  ∀ x : a -[r]→* b, x.IsReduced → x.length ≤ (longestBetween r a b hbot htop).length :=
  (exists_longest_iff_bot_lt_codim_lt_top a b).mp ⟨hbot,htop⟩ |>.choose_spec.right

@[simp]
lemma length_longestBetween_eq_eCodim {a b : α} (hbot : ⊥ < Rel.eCodim r a b) (htop : Rel.eCodim r a b < ⊤) :
    (longestBetween r a b hbot htop).length = Rel.eCodim r a b := by
  apply le_antisymm
  · exact length_le_eCodim_of_isReduced (longestBetween_isReduced hbot htop)
  · rw [eCodim_le_nat_iff]
    intro x
    exact longestBetween_longest hbot htop _ (reduce_isReduced _)

lemma maximal_of_IsReduced_of_length_eq_eCodim {a b : α} (x : a -[r]→* b) (hx : x.IsReduced) (hlength : x.length = Rel.eCodim r a b) :
    Maximal (·.IsReduced) x := by
  constructor
  · exact hx
  intro y hy hxy
  apply Eq.ge
  apply eq_of_le_of_length_le hx hxy
  suffices (y.length : WithBot ℕ∞) ≤ x.length by simpa
  rw [hlength]
  exact length_le_eCodim_of_isReduced hy

lemma maximal_longestBetween {a b : α} (hbot : ⊥ < Rel.eCodim r a b) (htop : Rel.eCodim r a b < ⊤) :
    Maximal (·.IsReduced) (longestBetween r a b hbot htop) :=
  maximal_of_IsReduced_of_length_eq_eCodim _ (longestBetween_isReduced _ _)
    (length_longestBetween_eq_eCodim hbot htop)

-- lemma length_le_length_longestBetween [r.IsDiscrete] (a b : α) (y : a -[r]→* b)
--     (z : Nonempty (a -[r]→* b) := ⟨y⟩) : y.length ≤ (@longestBetween _ r _ a b).length :=
--   (isDiscrete_iff_exists_longest_of_nonempty.mp (by assumption) a b
--     (by assumption)).choose_spec y

end longestBetween

section Rel.IsCatenary

instance [r.IsCatenary] : r.IsDiscrete where
  isDiscrete a b := ‹r.IsCatenary›.isCatenary a b |>.elim (fun hn =>
    ⟨·,(hn · |>.elim (fun hy => ⟨·,⟨hy.left,⟨hy.right.left,hy.right.right.le⟩⟩⟩))⟩)

end Rel.IsCatenary

section extendToCodim

/-- like `maximalExtension`, but with `r.IsCatenary` as instance argument -/
noncomputable def extendToCodim [r.IsCatenary] {a b : α} (x : a -[r]→* b) : a -[r]→* b :=
  ((‹r.IsCatenary›.isCatenary a b).choose_spec x).choose

@[simp]
lemma extendToCodim_isReduced [r.IsCatenary] {a b : α} (x : a -[r]→* b) :
    x.extendToCodim.IsReduced :=
  ((‹r.IsCatenary›.isCatenary a b).choose_spec x).choose_spec.left

lemma self_le_extendToCodim [r.IsCatenary] {a b : α} (x : a -[r]→* b) :
    x ≤ x.extendToCodim :=
  ((‹r.IsCatenary›.isCatenary a b).choose_spec x).choose_spec.right.left

private lemma extendToCodim_length_eq [r.IsCatenary] {a b : α} (x : a -[r]→* b) :
    x.extendToCodim.length = (‹r.IsCatenary›.isCatenary a b).choose :=
  ((‹r.IsCatenary›.isCatenary a b).choose_spec x).choose_spec.right.right

lemma maximal_extendToCodim [r.IsCatenary] {a b : α} (x : a -[r]→* b) :
    Maximal (·.IsReduced) x.extendToCodim := by
  constructor
  · exact extendToCodim_isReduced x
  · intro y hy hle
    apply Eq.ge
    apply eq_of_le_of_length_le (extendToCodim_isReduced x) hle
    rw [extendToCodim_length_eq x,← extendToCodim_length_eq y]
    apply hy.isReduced
    exact self_le_extendToCodim y

lemma extendToCodim_eq_self_of_maximal [r.IsCatenary] {a b : α} (x : a -[r]→* b) :
    Maximal (·.IsReduced) x → x.extendToCodim = x := by
  intro h
  have := self_le_extendToCodim x
  apply le_antisymm_of_isReduced_of_isReduced (extendToCodim_isReduced x) h.left _ this
  use h.right (extendToCodim_isReduced x) this

lemma length_eq_eCodim_of_maximal [r.IsCatenary] {a b : α} (x : a -[r]→* b) :
    Maximal (·.IsReduced) x → x.length = Rel.eCodim r a b := by
  intro h
  rw [← extendToCodim_eq_self_of_maximal _ h, extendToCodim_length_eq,
    ← extendToCodim_length_eq (longestBetween r a b ?a ?b),
    extendToCodim_eq_self_of_maximal _ (maximal_longestBetween ?a ?b),
    length_longestBetween_eq_eCodim]
  · refine bot_lt_eCodim_iff.mpr ⟨x⟩
  · exact eCodim_lt_top a b

lemma length_extendToCodim_eq_eCodim [r.IsCatenary] {a b : α} (x : a -[r]→* b) :
    x.extendToCodim.length = Rel.eCodim r a b :=
  length_eq_eCodim_of_maximal x.extendToCodim (maximal_extendToCodim x)

lemma maximal_append {a b c : α} {x : a -[r]→* b} {y : b -[r]→* c} : Maximal (·.IsReduced) x ∧ Maximal (·.IsReduced) y ↔
    Maximal (·.IsReduced) (x ++ y) := by
  constructor
  · intro ⟨hx,hy⟩
    use (append_isReduced.mpr ⟨hx.left,hy.left⟩)
    intro z hz
    intro h
    obtain ⟨x',y',rfl,hx',hy'⟩ := exists_eq_append_of_append_le _ _ _ h
    rw [append_isReduced] at hz
    apply append_le_append (hx.right hz.left hx') (hy.right hz.right hy')
  · rintro ⟨h,h'⟩
    rw [append_isReduced] at h
    constructor
    · use h.left
      intro x' hx' hxx'
      specialize h' (append_isReduced.mpr ⟨hx',h.right⟩) (append_left_mono _ hxx')
      apply Eq.ge
      apply append_left_injective y
      apply le_antisymm_of_isReduced_of_isReduced (append_isReduced.mpr h)
        (append_isReduced.mpr ⟨hx',h.right⟩) (append_left_mono y hxx') h'
    · use h.right
      intro y' hy' hyy'
      specialize h' (append_isReduced.mpr ⟨h.left,hy'⟩) (append_right_mono _ hyy')
      apply Eq.ge
      apply append_right_injective x
      exact le_antisymm_of_isReduced_of_isReduced (append_isReduced.mpr h) (append_isReduced.mpr ⟨h.left,hy'⟩)
        (append_right_mono x hyy') h'

end extendToCodim

section Rel.IsCatenary

lemma isCatenary_iff_length_eq_eCodim_of_maximal : r.IsCatenary ↔ ∀ ⦃a b : α⦄, Rel.eCodim r a b < ⊤ ∧ ∀ x : a -[r]→* b,
    Maximal (·.IsReduced) x → x.length = Rel.eCodim r a b := by
  refine ⟨fun r ⦃a b⦄ ↦ ⟨eCodim_lt_top a b, fun x hmax ↦ length_eq_eCodim_of_maximal x hmax⟩,?_⟩
  intro h
  constructor
  intro a b
  use ((Rel.eCodim r a b).unbotD 0).toNat
  intro x
  have : Rel.eCodim r a b ≠ ⊥ := (bot_lt_eCodim_iff.mpr ⟨x⟩).ne.symm
  rw [(WithBot.unbotD_eq_iff (y := (Rel.eCodim r a b).unbot this)).mpr (.inl
    ((WithBot.unbot_eq_iff this).mp rfl))]
  obtain ⟨hcodim,h⟩ := @h a b
  use x.maximalExtension hcodim,(maximal_maximalExtension hcodim x).left, (self_le_maximalExtension hcodim x)
  specialize h (x.maximalExtension hcodim) (maximal_maximalExtension hcodim x)
  simp_rw [← h]
  exact rfl

end Rel.IsCatenary

lemma dimension_formula [r.IsCatenary] {a b c : α} (x : a -[r]→* b) (y : b -[r]→* c):
  Rel.eCodim r a b + Rel.eCodim r b c = Rel.eCodim r a c := by
  rw [← length_eq_eCodim_of_maximal (x.maximalExtension (eCodim_lt_top a b))
      (maximal_maximalExtension (eCodim_lt_top a b) x),
    ← length_eq_eCodim_of_maximal (y.maximalExtension (eCodim_lt_top b c))
      (maximal_maximalExtension (eCodim_lt_top b c) y)]
  rw [← WithBot.coe_natCast, ← WithBot.coe_natCast (maximalExtension _ y).length]
  rw [← WithBot.coe_add,← ENat.coe_add, WithBot.coe_natCast,← length_append]
  refine
    length_eq_eCodim_of_maximal
      (maximalExtension (eCodim_lt_top a b) x ++ maximalExtension (eCodim_lt_top b c) y) ?_
  rw [← maximal_append]
  constructor
  · exact maximal_maximalExtension (eCodim_lt_top a b) x
  · exact maximal_maximalExtension (eCodim_lt_top b c) y

lemma isCatenary_iff_isDiscrete_and_dimension_formula : r.IsCatenary ↔ r.IsDiscrete ∧
    ∀ {a b c}, (a -[r]→* b) → (b -[r]→* c) →  Rel.eCodim r a b + Rel.eCodim r b c = Rel.eCodim r a c := by
  constructor
  · intro h
    constructor
    · exact instIsDiscreteOfIsCatenary
    · exact fun {a b c} a_1 a_2 ↦ dimension_formula a_1 a_2
  · rintro ⟨hl,hr⟩
    have hlt_top:= isDiscrete_iff_forall_eCodim_lt_top.mp hl
    rw [isCatenary_iff_length_eq_eCodim_of_maximal]
    intro a b
    -- specialize hlt_top a b
    use hlt_top a b
    intro x hx
    have hbot_lt : ⊥ < Rel.eCodim r a b := by
      refine bot_lt_eCodim_iff.mpr ⟨x⟩
    induction x with
    | singleton a =>
      specialize hr (singleton a) (singleton a)
      simp only [length_singleton, Nat.cast_zero]
      simp_rw [← length_longestBetween_eq_eCodim hbot_lt (hlt_top a a)] at ⊢ hr
      simp_rw [← WithBot.coe_zero, ← WithBot.coe_natCast] at hr ⊢
      simp only [WithBot.coe_zero, WithBot.zero_eq_coe, Nat.cast_eq_zero] at ⊢
      norm_cast at hr
      exact Nat.self_eq_add_right.mp (id (Eq.symm hr))
    | cons a l hab ih =>
      specialize hr (ofRel hab) l
      rw [← hr] at hbot_lt ⊢
      simp only [WithBot.bot_lt_add] at hbot_lt
      rw [← ofRel_append, ← maximal_append] at hx
      specialize ih hx.right hbot_lt.right
      rw [← ofRel_append,length_append, Nat.cast_add, ih]
      congr
      rw [eCodim_eq_one_of_maximal_ofRel _ hx.left,length_ofRel,Nat.cast_one]


-- -- variable (r) in
-- noncomputable def longerBetween [r.IsDense] {a b : α} (y : a -[r]→* b) : a -[r]→* b :=
--   (‹r.IsDense›.isDense a b y).choose

-- lemma length_lt_length_longerBetween [r.IsDense] {a b : α} (y : a -[r]→* b) :
--   y < (longerBetween y) :=
--   (‹r.IsDense›.isDense a b y).choose_spec

-- instance [r.IsDense] : Rel.IsDense (Function.swap r) where
--   isDense a b x := (Rel.IsDense.isDense r b a x.reverse).elim (fun h => ⟨·.reverse,by

--     simp_all⟩)

-- instance [r.IsDiscrete] : Rel.IsDiscrete (Function.swap r) where
--   isDiscrete a b := (Rel.IsDiscrete.isDiscrete r b a).elim (fun h => ⟨·,(by
--     specialize h ·.reverse
--     simp_all)⟩)

-- section
-- variable {a b : α} {s : a -[r]→* b} {x : α}

-- theorem subsingleton_of_length_eq_zero (hs : s.length = 0) : {x | x ∈ s}.Subsingleton := by
--   rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
--   congr!
--   exact finCongr (by rw [hs, zero_add]) |>.injective <| Subsingleton.elim (α := Fin 1) _ _

-- theorem length_ne_zero_of_nontrivial (h : {x | x ∈ s}.Nontrivial) : s.length ≠ 0 :=
--   fun hs ↦ h.not_subsingleton <| subsingleton_of_length_eq_zero hs

-- theorem length_pos_of_nontrivial (h : {x | x ∈ s}.Nontrivial) : 0 < s.length :=
--   Nat.pos_iff_ne_zero.mpr <| length_ne_zero_of_nontrivial h

-- theorem length_ne_zero (irrefl : Irreflexive r) : s.length ≠ 0 ↔ {x | x ∈ s}.Nontrivial := by
--   refine ⟨?_,length_ne_zero_of_nontrivial⟩
--   intro h
--   contrapose! h
--   simp only [Set.not_nontrivial_iff] at h
--   cases s with
--   | singleton a => rfl
--   | @cons a c _ l hab =>
--     apply (irrefl a).elim
--     convert hab
--     apply h <;> simp

-- theorem length_pos (irrefl : Irreflexive r) : 0 < s.length ↔ {x | x ∈ s}.Nontrivial :=
--   Nat.pos_iff_ne_zero.trans <| length_ne_zero irrefl

-- lemma length_eq_zero (irrefl : Irreflexive r) : s.length = 0 ↔ {x | x ∈ s}.Subsingleton := by
--   rw [← not_ne_iff, length_ne_zero irrefl, Set.not_nontrivial_iff]

-- end
end RelSeriesHT
