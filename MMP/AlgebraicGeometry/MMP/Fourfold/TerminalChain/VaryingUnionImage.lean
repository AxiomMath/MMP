module

public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.VaryingLabelCodimension

/-!
# The varying union maps to a set of dimension at most one

Let `(p_i, Θ_i)_{i ≥ 0}`, `p_i : Y_i ⟶ X_i`, be a terminal chain over a stabilized small klt
tail `(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}` of fourfolds. There is an index `i₁` such that for
every `i ≥ i₁` the image under `p_i` of the reduced union `⋃ S_h^{Y_i}` of the varying labels on
`Y_i` is a closed subset of `X_i` of dimension at most one.

## Main results

* `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.exists_isClosed_image_varyingLabels`:
  from some junction on, `p_i` maps the reduced union of the varying labels onto a closed set of
  topological Krull dimension at most `1`.

## Implementation notes

* The reduced union of the varying labels on `Y_i` is the union of the supports of the prime
  divisors `P` of `Y_i` with `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsLabelCentre`
  for a varying label, exactly as in the field
  `MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.topologicalKrullDim_image_varyingLabels_le`
  of a prepared chain, so the result supplies those fields directly.
* The image is also asserted to be closed, as `p_i` is proper and there are finitely many
  labels; dimension is `topologicalKrullDim` of the image.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold

namespace StabilizedSmallKltTail

namespace TerminalChain

variable {T : StabilizedSmallKltTail}

/-- The valuation of `k(X_j)` corresponding to a valuation of `k(X_0)` is unique. -/
private theorem corresponds_unique
    {ξ : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ))} :
    ∀ {j : ℕ} {η₁ η₂ : Valuation (T.X j).functionField (WithZero (Multiplicative ℤ))},
      T.Corresponds j ξ η₁ → T.Corresponds j ξ η₂ → η₁ = η₂
  | 0, _, _, h₁, h₂ => h₁.trans h₂.symm
  | j + 1, _, _, ⟨ζ₁, h₁, t₁⟩, ⟨ζ₂, h₂, t₂⟩ => by
    obtain rfl := corresponds_unique h₁ h₂
    have hb := (T.isFourfoldStepDiagram j).isSmallMorphism_plus.isBirationalMorphism
    exact MMP.Fourfold.Oai4C1.valuation_eq_of_comap_eq hb.functionFieldMap_bijective.2
      (t₁.trans t₂.symm)

/-- In `WithBot ℕ∞`, `a + 3 ≤ 4` forces `a ≤ 1`. -/
private theorem le_one_of_add_three_le_four {a : WithBot ℕ∞} (h : a + 3 ≤ 4) : a ≤ 1 := by
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe n =>
    have h' : n + 3 ≤ 4 := by
      rw [← WithBot.coe_le_coe]
      simpa using h
    induction n using ENat.recTopCoe with
    | top => simp at h'
    | coe m =>
      norm_cast at h' ⊢
      omega

variable (C : TerminalChain T) (i : ℕ)

/-- A prime divisor `P` of `Y_i` is the divisor `(Y_i, p_i, P)` over `X_i`. -/
private noncomputable def divisorOver (P : MMP.Mori.PrimeDivisor (C.junction i).Y) :
    MMP.Mori.DivisorOver ℂ (T.sX i) :=
  ⟨_, (C.junction i).p, (C.junction i).isQFactorial.1, (C.junction i).isBirationalMorphism, P⟩

/-- Since `p_i` is proper, the image of a prime divisor of `Y_i` is closed. -/
private theorem isClosed_image_support (P : MMP.Mori.PrimeDivisor (C.junction i).Y) :
    IsClosed ((C.junction i).p '' P.support) := by
  haveI := isProper_of_isProjectiveMorphism _ (C.junction i).isProjectiveMorphism
  exact (C.junction i).p.isClosedMap _
    (AlgebraicGeometry.PrimeDivisor.support_eq_closure P ▸ isClosed_closure)

/-- The centre on `X_i` of `(Y_i, p_i, P)` is `p_i(P)`. -/
private theorem coe_center_divisorOver (P : MMP.Mori.PrimeDivisor (C.junction i).Y) :
    ((divisorOver C i P).center : Set (T.X i)) = (C.junction i).p '' P.support := by
  rw [MMP.Mori.DivisorOver.coe_center]
  exact (isClosed_image_support C i P).closure_eq

/-- If the centre of `(Y_i, p_i, P)` has codimension at least three in the fourfold `X_i`, then
`p_i(P)` has dimension at most one. -/
private theorem topologicalKrullDim_image_support_le_one
    (P : MMP.Mori.PrimeDivisor (C.junction i).Y)
    (h : 3 ≤ codimension (divisorOver C i P).center) :
    topologicalKrullDim ((C.junction i).p '' P.support) ≤ 1 := by
  haveI : LocallyOfFiniteType (T.sX i) :=
    (T.isFourfoldStepDiagram i).isNormalVariety_minus.1.toLocallyOfFiniteType
  have hsum := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (T.sX i)
    ((divisorOver C i P).f (divisorOver C i P).E.genericPoint)
  rw [← MMP.Mori.DivisorOver.center_eq_closure_genericPoint, coe_center_divisorOver,
    (C.junction i).dim_base] at hsum
  rw [MMP.Positivity.DivisorOver.codimension_center] at h
  refine le_one_of_add_three_le_four (hsum ▸ ?_)
  gcongr
  exact WithBot.coe_le_coe.mpr h

/-- Two centres on `Y_i` of the same label have the same image on `X_i`. -/
private theorem image_support_eq_of_isLabelCentre {S : C.Label}
    {P P' : MMP.Mori.PrimeDivisor (C.junction i).Y} (hP : C.IsLabelCentre S ⟨i, none⟩ P)
    (hP' : C.IsLabelCentre S ⟨i, none⟩ P') :
    (C.junction i).p '' P.support = (C.junction i).p '' P'.support := by
  obtain ⟨w, hw, hDw⟩ := hP
  obtain ⟨w', hw', hDw'⟩ := hP'
  obtain rfl := corresponds_unique hw hw'
  rw [← coe_center_divisorOver, ← coe_center_divisorOver,
    MMP.Positivity.DivisorOver.center_eq_of_valuation_eq
      (T.isFourfoldStepDiagram i).isNormalVariety_minus.1
      (show (divisorOver C i P).valuation = (divisorOver C i P').valuation from
        hDw.trans hDw'.symm)]

/-- The image on `X_i` of the centres on `Y_i` of one label is empty or the image of any one of
them. -/
private theorem image_labelCentres_eq (S : C.Label) :
    (C.junction i).p '' {y | ∃ P : MMP.Mori.PrimeDivisor (C.model ⟨i, none⟩),
        C.IsLabelCentre S ⟨i, none⟩ P ∧ y ∈ P.support} = ∅ ∨
      ∃ P, C.IsLabelCentre S ⟨i, none⟩ P ∧
        (C.junction i).p '' {y | ∃ P : MMP.Mori.PrimeDivisor (C.model ⟨i, none⟩),
          C.IsLabelCentre S ⟨i, none⟩ P ∧ y ∈ P.support} = (C.junction i).p '' P.support := by
  by_cases h : ∃ P, C.IsLabelCentre S ⟨i, none⟩ P
  · obtain ⟨P₀, hP₀⟩ := h
    refine .inr ⟨P₀, hP₀, subset_antisymm ?_ (Set.image_mono fun y hy => ⟨P₀, hP₀, hy⟩)⟩
    rintro _ ⟨y, ⟨P, hP, hy⟩, rfl⟩
    exact image_support_eq_of_isLabelCentre C i hP hP₀ ▸ Set.mem_image_of_mem _ hy
  · refine .inl (Set.image_eq_empty.mpr (Set.eq_empty_of_forall_notMem ?_))
    rintro y ⟨P, hP, -⟩
    exact h ⟨P, hP⟩

/-- For a terminal chain over a stabilized small klt tail there is `i₁` such that for every
`i ≥ i₁` the junction morphism `p_i : Y_i ⟶ X_i` maps the reduced union of the varying labels
on `Y_i` onto a closed subset of `X_i` of topological Krull dimension at most one. -/
@[mmp "prop_oai4_codim_two_d"]
theorem exists_isClosed_image_varyingLabels :
    ∃ i₁ : ℕ, ∀ i ≥ i₁,
      IsClosed ((C.junction i).p ''
          {y : (C.junction i).Y | ∃ S : C.Label, C.IsVaryingLabel S ∧
            ∃ P : MMP.Mori.PrimeDivisor (C.model ⟨i, none⟩),
              C.IsLabelCentre S ⟨i, none⟩ P ∧ y ∈ P.support}) ∧
      topologicalKrullDim ((C.junction i).p ''
          {y : (C.junction i).Y | ∃ S : C.Label, C.IsVaryingLabel S ∧
            ∃ P : MMP.Mori.PrimeDivisor (C.model ⟨i, none⟩),
              C.IsLabelCentre S ⟨i, none⟩ P ∧ y ∈ P.support}) ≤ 1 := by
  classical
  obtain ⟨i₁, h₃⟩ := C.exists_three_le_codimension_of_isVaryingLabel
  refine ⟨i₁, fun i hi => ?_⟩
  haveI := C.finite_label
  haveI : Fintype C.Label := Fintype.ofFinite _
  let A : C.Label → Set (T.X i) := fun S => (C.junction i).p '' {y |
    ∃ P : MMP.Mori.PrimeDivisor (C.model ⟨i, none⟩), C.IsLabelCentre S ⟨i, none⟩ P ∧ y ∈ P.support}
  have hU : (C.junction i).p '' {y : (C.junction i).Y | ∃ S : C.Label, C.IsVaryingLabel S ∧
      ∃ P : MMP.Mori.PrimeDivisor (C.model ⟨i, none⟩), C.IsLabelCentre S ⟨i, none⟩ P ∧
        y ∈ P.support} = ⋃ S ∈ Finset.univ.filter C.IsVaryingLabel, A S := by
    ext x
    simp only [A, Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq, Finset.mem_filter,
      Finset.mem_univ, true_and, exists_prop]
    exact ⟨fun ⟨y, ⟨S, hS, P, hP, hy⟩, hx⟩ => ⟨S, hS, y, ⟨P, hP, hy⟩, hx⟩,
      fun ⟨S, hS, y, ⟨P, hP, hy⟩, hx⟩ => ⟨y, ⟨S, hS, P, hP, hy⟩, hx⟩⟩
  have hA : ∀ S, IsClosed (A S) := fun S => by
    rcases image_labelCentres_eq C i S with h | ⟨P, -, h⟩ <;> simp only [A, h]
    exacts [isClosed_empty, isClosed_image_support C i P]
  rw [hU]
  refine ⟨(Finset.finite_toSet _).isClosed_biUnion fun S _ => hA S,
    topologicalKrullDim_biUnion_le _ hA fun S hS => ?_⟩
  rcases image_labelCentres_eq C i S with h | ⟨P, ⟨w, hw, hP⟩, h⟩ <;> rw [show A S = _ from h]
  · exact (Order.krullDim_eq_bot_iff.mpr ⟨fun Z => Z.isIrreducible.nonempty.some.2⟩).le.trans
      bot_le
  · exact topologicalKrullDim_image_support_le_one C i P
      (h₃ i hi S (Finset.mem_filter.mp hS).2 w hw _ ⟨divisorOver C i P,
        isProper_of_isProjectiveMorphism _ (C.junction i).isProjectiveMorphism, hP.symm, rfl⟩)

end TerminalChain

end StabilizedSmallKltTail

end MMP.Fourfold
