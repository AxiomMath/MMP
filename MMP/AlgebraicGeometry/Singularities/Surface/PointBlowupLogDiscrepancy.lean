module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGermTypes
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
public import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
public import MMP.AlgebraicGeometry.MMP.Abundance.Basic
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.EntryIndex

/-!
# The log discrepancy vector after blowing up a point

Let `(X, P; B)` be a surface germ with boundary, `g : Y ⟶ X` a resolution of `(X, P)` with
exceptional curves `E_1, …, E_n` and log discrepancy vector `a`, `y ∈ g⁻¹(P)` a closed point,
`π : Y' ⟶ Y` the blow-up of `y` and `F = π⁻¹(y)_red` its exceptional curve. Then `g ∘ π` is a
resolution of `(X, P)` whose exceptional curves are the birational transforms `E'_j = π⁻¹_* E_j`
and `F`, and its log discrepancy vector `a'` is `a'_{E'_j} = a_j`, `a'_F = 2 - mult_y Θ_{g,a}`,
where `Θ_{g,a} = g⁻¹_* B + ∑_j (1 - a_j) E_j`.

The proof follows the source. The blow-up is an isomorphism off `y`, so `g ∘ π` is an
isomorphism over `X ∖ {P}`; the irreducible components of `(g ∘ π)⁻¹(P) = π⁻¹(g⁻¹(P))` are the
`E'_j` and `F`: a curve of `Y'` mapping to `y` is `F`, and one that does not is the birational
transform of the curve of `Y` through the image of its generic point. With `D = K_Y + Θ` and
`K_{Y'} = π^* K_Y + F`, the formula `π^* C = π⁻¹_* C + (mult_y C) F` for curves gives
`π^* D = K_{Y'} + (g ∘ π)⁻¹_* B + ∑_j (1 - a_j) E'_j + (1 - (2 - mult_y Θ)) F`, and the
projection formula gives `(π^* D · E'_j) = (D · E_j) = 0` and `(π^* D · F) = 0`.

## Main results

* `MMP.Flips.IsGermResolution.comp_blowUpToBase`: `g ∘ π` is a resolution of `(X, P)`.
* `MMP.Flips.IsExceptionalCurveEnumeration.snoc_blowUp`: its exceptional curves are
  `E'_1, …, E'_n, F`.
* `MMP.Flips.IsGermResolution.inverseTransformDivisor_comp_blowUpToBase`:
  `(g ∘ π)⁻¹_* B = π⁻¹_* g⁻¹_* B`.
* `MMP.Flips.exists_isIntersectionNumber_totalTransform`,
  `MMP.Flips.isIntersectionNumber_totalTransform_exceptional`: for every `ℚ`-divisor `D` on `Y`,
  `((π⁻¹_* D + (mult_y D) F) · E'_j) = (D · E_j)` and `((π⁻¹_* D + (mult_y D) F) · F) = 0`.
* `MMP.Flips.isGermLogDiscrepancyVector_snoc_blowUp_of_isCanonicalDivisor`: the vector
  `(a_1, …, a_n, 2 - mult_y Θ_{g,a})` is a log discrepancy vector on `g ∘ π`, given a canonical
  divisor `K_Y` with `π^* K_Y + F` canonical on `Y'`.
* `MMP.Flips.isGermLogDiscrepancyVector_snoc_blowUp_iff_of_isCanonicalDivisor`: the statement,
  for `π^* K_Y + F` canonical on `Y'` for every canonical divisor `K_Y` of `Y`.

## Implementation notes

The ground field is algebraically closed, as for the pull-back formula
`MMP.Threefold.Resolution.pullback_single_blowUp_singleton`. The blow-up is
`AlgebraicGeometry.blowUp` of the reduced point `y`, and `F` is a prime divisor whose ideal sheaf
is `AlgebraicGeometry.exceptionalIdeal`. The exceptional curves of `g ∘ π` are listed as
`Fin.snoc E' F`, `F` being the last one, and the log discrepancy vector as
`Fin.snoc a (2 - mult_y Θ_{g,a})`. The statement that `a'` is the log discrepancy vector is the
equivalence "`a'` is a log discrepancy vector on `g ∘ π` iff `a' = (a, 2 - mult_y Θ_{g,a})`",
which contains its existence and uniqueness.

The canonical divisor of `Y'` is a genuine canonical divisor, `π^* K_Y + F`, not a transform of
`K_Y`; that it is canonical is a hypothesis here.

The total transform of a `ℚ`-divisor `D` is written `π⁻¹_* D + (mult_y D) F`, which is `π^* D` by
`MMP.Threefold.Resolution.pullback_qDivisor_blowUp_singleton`; intersection numbers are computed
curve by curve from the projection formula
`MMP.Mori.Divisor.degreeOn_pullback_eq_degree_pushforward`, the push-forward of `E'_j` being
`E_j` with degree `1` since `π` is an isomorphism at the generic point of `E'_j`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 3.1.4, 3.1.5,
  3.3.2
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Flips

/-! ### Prime divisors and inverse transforms -/

section Helpers

variable {X Y : Scheme.{u}}

/-- A prime divisor `D` of `Y` whose generic point lies in the biregular locus of `g : X ⟶ Y`
has a birational transform `g⁻¹_* D`, whose generic point maps to that of `D`. -/
theorem exists_inverseTransformPrimeDivisor_eq_some {g : X ⟶ Y} (D : Mori.PrimeDivisor Y)
    (hD : D.genericPoint ∈ biregularLocus g) :
    ∃ D' : Mori.PrimeDivisor X, inverseTransformPrimeDivisor g D = some D' ∧
      g D'.genericPoint = D.genericPoint := by
  set V := biregularLocus g
  have : IsIso (g ∣_ V) := isBiregular_biregularLocus g
  obtain ⟨p, hp⟩ := (g ∣_ V).surjective ⟨D.genericPoint, hD⟩
  have hgx : g ((g ⁻¹ᵁ V).ι p) = D.genericPoint := by
    have e : V.ι ((g ∣_ V) p) = g ((g ⁻¹ᵁ V).ι p) := by
      rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
    rw [← e, hp]; rfl
  have hcoh : Order.coheight ((g ⁻¹ᵁ V).ι p) = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus g (hgx ▸ hD), hgx]
    exact D.coheight_genericPoint
  set D' : Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh
  have hη : Mori.PrimeDivisor.genericPoint D' = (g ⁻¹ᵁ V).ι p :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcoh
  refine ⟨D', ?_, by rw [hη, hgx]⟩
  exact MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
    (by rw [hη, hgx]) (by rw [hη, hgx]; exact hD)

/-- The dimension of a closed subscheme is the dimension of its support. -/
theorem topologicalKrullDim_subscheme (I : Y.IdealSheafData) :
    topologicalKrullDim I.subscheme = topologicalKrullDim (I.support : Set Y) := by
  have h :=
    I.subschemeι.isClosedEmbedding.toIsEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq
  rwa [Scheme.IdealSheafData.range_subschemeι] at h

/-- A prime divisor of a surface (a variety of dimension two) is a curve. -/
theorem isCurveIn_idealSheaf_of_topologicalKrullDim_eq_two {k : Type u} [Field k]
    {sY : Y ⟶ Spec (.of k)} (hY : Mori.IsVariety k sY) (hYd : topologicalKrullDim Y = 2)
    (D : Mori.PrimeDivisor Y) : IsCurveIn D.idealSheaf := by
  have : IsIntegral Y := hY.toIsIntegral
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  refine ⟨D.integral, ?_⟩
  have h := topologicalKrullDim_closure_singleton_add_coheight sY D.genericPoint
  rw [D.coheight_genericPoint, hYd] at h
  rw [topologicalKrullDim_subscheme]
  change topologicalKrullDim (D.support : Set Y) = 1
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  generalize topologicalKrullDim (closure {D.genericPoint} : Set Y) = d at h ⊢
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => exact absurd h (by decide)
    | coe d =>
      have h' : ((d + 1 : ℕ) : ℕ∞) = ((2 : ℕ) : ℕ∞) := WithBot.coe_injective (by push_cast; exact h)
      obtain rfl : d = 1 := by
        have := Nat.cast_injective h'
        omega
      rfl

/-- **Maximality of prime divisors.** In an irreducible scheme, the support of a prime divisor
contained in a proper closed subset `S` is maximal among the irreducible subsets of `S`. -/
theorem maximal_support_of_subset [IrreducibleSpace Y] {S : Set Y} (hS : IsClosed S)
    (hSne : S ≠ Set.univ) (D : Mori.PrimeDivisor Y) (hDS : (D.support : Set Y) ⊆ S) :
    Maximal (fun Z : Set Y => IsIrreducible Z ∧ Z ⊆ S) D.support := by
  refine ⟨⟨?_, hDS⟩, fun Z hZ hDZ => ?_⟩
  · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure
  have hζ := hZ.1.isGenericPoint_genericPoint_closure
  set ζ := hZ.1.genericPoint
  have hηmem : D.genericPoint ∈ closure ({ζ} : Set Y) := by
    rw [hζ.def]
    refine subset_closure (hDZ ?_)
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have hle : D.genericPoint ≤ ζ := specializes_iff_mem_closure.mpr hηmem
  by_cases heq : ζ = D.genericPoint
  · intro z hz
    have : z ∈ closure Z := subset_closure hz
    rw [← hζ.def, heq, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
    exact this
  · exfalso
    have hlt : D.genericPoint < ζ :=
      lt_iff_le_not_ge.mpr ⟨hle, fun h' => heq (Specializes.antisymm hle h').eq⟩
    have hstep := Order.coheight_add_one_le hlt
    rw [D.coheight_genericPoint] at hstep
    have h0 : Order.coheight ζ = 0 := by
      by_contra h0
      have h1 : 1 ≤ Order.coheight ζ := Order.one_le_iff_ne_zero.mpr h0
      have : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) hstep
      exact absurd this (by decide)
    have hmax : IsMax ζ := Order.coheight_eq_zero.mp h0
    have hgen : genericPoint Y ⤳ ζ := (genericPoint_spec Y).specializes (Set.mem_univ _)
    have hge : ζ ≤ genericPoint Y := hgen
    have hζgen : genericPoint Y ≤ ζ := hmax hge
    apply hSne
    rw [Set.eq_univ_iff_forall]
    intro z
    have h1 : genericPoint Y ∈ closure ({ζ} : Set Y) := specializes_iff_mem_closure.mp hζgen
    have hz : z ∈ closure ({ζ} : Set Y) :=
      closure_minimal (Set.singleton_subset_iff.mpr h1) isClosed_closure
        (by rw [(genericPoint_spec Y).def]; trivial)
    rw [hζ.def] at hz
    exact (closure_minimal hZ.2 hS) hz

end Helpers

/-! ### The blow-up of a point of a resolution -/

section Blowup

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X}
  {g : Y ⟶ X} [QuasiCompact (g ≫ sX)] [IsNormal Y]

open MMP.Threefold.Resolution

/-- A surface germ has a point other than `P`. -/
theorem exists_ne_of_isSurfaceGerm (h : IsSurfaceGerm sX P) : ∃ x : X, x ≠ P := by
  by_contra hall
  push Not at hall
  have : Subsingleton X := ⟨fun a b => (hall a).trans (hall b).symm⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology X
  rw [h.2.1] at h0
  exact absurd h0 (by decide)

variable [IsAlgClosed k]

/-- **The blow-up of a point over `P` is again a resolution.** If `g : Y ⟶ X` is a resolution of
`(X, P)` and `π : Y' ⟶ Y` the blow-up of a closed point `y ∈ g⁻¹(P)`, then `g ∘ π` is a
resolution of `(X, P)`. -/
theorem IsGermResolution.comp_blowUpToBase (hg : IsGermResolution sX P g) {y : Y}
    (hy : IsClosed ({y} : Set Y)) (hyP : g y = P) :
    IsGermResolution sX P
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ≫ g) := by
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y) with hIdef
  have hYv := hg.isVariety
  have hYd := hg.topologicalKrullDim_eq
  have hYs := hg.isSmoothResolution.isSmoothScheme
  have hXv : Mori.IsVariety k sX := hg.isSurfaceGerm.1.1
  have hvar : Mori.IsVariety k ((blowUpToBase I ≫ g) ≫ sX) := by
    rw [Category.assoc]; exact isVariety_blowUp_singleton hYv hYd hy
  have : LocallyOfFiniteType (g ≫ sX) := hYv.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sX)
  have : IsProper (blowUpToBase I) :=
    TwoStepTower.isProper_blowUpToBase (TwoStepTower.isFiniteType_of_isLocallyNoetherian I)
  have : IsProper g := hg.isSmoothResolution.isProper
  have : IrreducibleSpace X := by have := hXv.toIsIntegral; infer_instance
  have : IrreducibleSpace (blowUp I) := by have := hvar.toIsIntegral; infer_instance
  obtain ⟨U, hU, hiso⟩ := hg.isIso_away
  have hle : g ⁻¹ᵁ U ≤ (⟨(I.support : Set Y)ᶜ, I.support.isClosed.isOpen_compl⟩ : Y.Opens) := by
    intro x hx
    change x ∉ (I.support : Set Y)
    rw [hIdef, support_vanishingIdeal_singleton hy]
    rintro rfl
    have : g x ∈ (U : Set X) := hx
    rw [hU, hyP] at this
    exact this rfl
  have : IsIso (blowUpToBase I ∣_ (⟨(I.support : Set Y)ᶜ, I.support.isClosed.isOpen_compl⟩ :
      Y.Opens)) := isIso_blowUp_restrict_compl_support I
  have h1 : IsIso (blowUpToBase I ∣_ (g ⁻¹ᵁ U)) :=
    MMP.Resolution.Kollar.isIso_morphismRestrict_of_le _ hle
  have hcomp : IsIso ((blowUpToBase I ≫ g) ∣_ U) := by
    rw [morphismRestrict_comp]; exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 hiso
  have hUne : ((U : Set X)).Nonempty := by
    obtain ⟨x, hx⟩ := exists_ne_of_isSurfaceGerm hg.isSurfaceGerm
    exact ⟨x, by rw [hU]; exact hx⟩
  have hU'ne : (((blowUpToBase I ≫ g) ⁻¹ᵁ U : (blowUp I).Opens) : Set (blowUp I)).Nonempty := by
    obtain ⟨x, hx⟩ := hUne
    obtain ⟨p, -⟩ := ((blowUpToBase I ≫ g) ∣_ U).surjective ⟨x, hx⟩
    exact ⟨p.1, p.2⟩
  have hbir : IsBirationalMorphism (blowUpToBase I ≫ g) :=
    isBirationalMorphism_of_isIso_resLE _ _ U hU'ne hUne le_rfl
      (by rw [Scheme.Hom.resLE_eq_morphismRestrict]; exact hcomp)
  refine ⟨hg.isSurfaceGerm, ⟨inferInstance, hbir, ?_⟩, ?_, U, hU, hcomp⟩
  · rw [Category.assoc]; exact isSmoothScheme_blowUp_singleton hYv hYs hYd hy
  · have : Mori.IsVariety k sX := hXv
    have : Mori.IsVariety k ((blowUpToBase I ≫ g) ≫ sX) := hvar
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX
      ((blowUpToBase I ≫ g) ≫ sX) hbir]
    exact hg.isSurfaceGerm.2.1

omit [IsAlgClosed k] [QuasiCompact (g ≫ sX)] [IsNormal Y] in
/-- A resolution of `(X, P)` has a point not over `P`. -/
theorem IsGermResolution.exists_map_ne (hg : IsGermResolution sX P g) : ∃ x : Y, g x ≠ P := by
  obtain ⟨U, hU, hiso⟩ := hg.isIso_away
  obtain ⟨x, hx⟩ := exists_ne_of_isSurfaceGerm hg.isSurfaceGerm
  have hxU : x ∈ U := by change x ∈ (U : Set X); rw [hU]; exact hx
  obtain ⟨p, hp⟩ := (g ∣_ U).surjective ⟨x, hxU⟩
  refine ⟨p.1, ?_⟩
  have : g p.1 = x := by
    have e : U.ι ((g ∣_ U) p) = g ((g ⁻¹ᵁ U).ι p) := by
      rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
    rw [← show (g ⁻¹ᵁ U).ι p = p.1 from rfl, ← e, hp]; rfl
  rw [this]; exact hx

omit [IsAlgClosed k] [QuasiCompact (g ≫ sX)] [IsNormal Y] in
/-- The fibre `g⁻¹(P)` of a resolution of `(X, P)` is a proper closed subset. -/
theorem IsGermResolution.isClosed_preimage_and_ne_univ (hg : IsGermResolution sX P g) :
    IsClosed (g.base ⁻¹' {P}) ∧ g.base ⁻¹' {P} ≠ Set.univ := by
  refine ⟨hg.isSurfaceGerm.2.2.1.preimage g.continuous, fun h => ?_⟩
  obtain ⟨x, hx⟩ := hg.exists_map_ne
  have : x ∈ g.base ⁻¹' {P} := h ▸ Set.mem_univ x
  exact hx this

set_option hygiene false in
/-- The blow-up `π : Y' ⟶ Y` of the reduced closed point `y`. -/
local notation "πy" => blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds _))

set_option hygiene false in
/-- The blow-up `Y'` of the reduced closed point `y`. -/
local notation "Y'y" => blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds _))

/-- **The exceptional curves after blowing up a point over `P`.** Let `g : Y ⟶ X` be a resolution
of `(X, P)` with exceptional curves `E_1, …, E_n`, `π : Y' ⟶ Y` the blow-up of a closed point
`y ∈ g⁻¹(P)` with exceptional curve `F`, and `E'_j = π⁻¹_* E_j`. Then `E'_1, …, E'_n, F` are the
exceptional curves of `g ∘ π`. -/
theorem IsExceptionalCurveEnumeration.snoc_blowUp [IsLocallyNoetherian Y]
    (hg : IsGermResolution sX P g) {n : ℕ} {E : Fin n → Mori.PrimeDivisor Y}
    (hE : IsExceptionalCurveEnumeration g P E) {y : Y} (hy : IsClosed ({y} : Set Y))
    (hyP : g y = P)
    {F : Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
    {E' : Fin n → Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))}
    (hE' : ∀ j, inverseTransformPrimeDivisor
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) (E j) = some (E' j)) :
    IsExceptionalCurveEnumeration
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ≫ g) P
      (Fin.snoc E' F : Fin (n + 1) → Mori.PrimeDivisor _) := by
  have hYv := hg.isVariety
  have hYd := hg.topologicalKrullDim_eq
  have hg' := hg.comp_blowUpToBase hy hyP
  have hvar : Mori.IsVariety k (πy ≫ g ≫ sX) := isVariety_blowUp_singleton hYv hYd hy
  have hY'd := hg'.topologicalKrullDim_eq
  have : IrreducibleSpace Y := by have := hYv.toIsIntegral; infer_instance
  have : IrreducibleSpace (Y'y) := by have := hvar.toIsIntegral; infer_instance
  obtain ⟨hScl, hSne⟩ := hg.isClosed_preimage_and_ne_univ
  obtain ⟨hS'cl, hS'ne⟩ := hg'.isClosed_preimage_and_ne_univ
  have hcoh2 : Order.coheight y = 2 := coheight_eq_two_of_isClosed hYv hYd hy
  -- the transforms `E'_j`
  have hmap : ∀ j, πy (E' j).genericPoint = (E j).genericPoint ∧
      πy (E' j).genericPoint ∈ biregularLocus πy := fun j =>
    map_genericPoint_of_inverseTransformPrimeDivisor_eq_some (hE' j)
  have hEP : ∀ j, g (E j).genericPoint = P := fun j =>
    (hE.isGermExceptionalCurve j).1.prop.2 (by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)
  have hEy : ∀ j, (E j).genericPoint ≠ y := fun j h => by
    have := (E j).coheight_genericPoint
    rw [h, hcoh2] at this
    exact absurd this (by decide)
  have hFmem : ∀ q, q ∈ F.support ↔ πy q = y :=
    mem_support_iff_of_idealSheaf_eq_exceptionalIdeal hy hF
  have hFη : πy F.genericPoint = y := (hFmem _).mp (by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)
  have hsub : ∀ D : Mori.PrimeDivisor (Y'y), (πy ≫ g) D.genericPoint = P →
      (D.support : Set (Y'y)) ⊆ (πy ≫ g).base ⁻¹' {P} := fun D hD => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact closure_minimal (Set.singleton_subset_iff.mpr hD) hS'cl
  have hexc : ∀ D : Mori.PrimeDivisor (Y'y), (πy ≫ g) D.genericPoint = P →
      IsGermExceptionalCurve (πy ≫ g) P D := fun D hD =>
    ⟨maximal_support_of_subset hS'cl hS'ne D (hsub D hD),
      isCurveIn_idealSheaf_of_topologicalKrullDim_eq_two hvar hY'd D⟩
  have hFP : (πy ≫ g) F.genericPoint = P := by
    rw [Scheme.Hom.comp_apply, hFη, hyP]
  refine ⟨Fin.snoc_injective_of_injective (fun i j hij => ?_) ?_, fun i => ?_, fun C hC => ?_⟩
  · apply hE.injective
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    have := (hmap i).1
    rw [hij, (hmap j).1] at this
    exact this.symm
  · rintro ⟨j, hj⟩
    apply hEy j
    rw [← (hmap j).1, hj, hFη]
  · induction i using Fin.lastCases with
    | last =>
      rw [Fin.snoc_last]; exact hexc F hFP
    | cast j =>
      rw [Fin.snoc_castSucc]
      exact hexc (E' j) (by rw [Scheme.Hom.comp_apply, (hmap j).1, hEP j])
  · -- an exceptional curve `C` of `g ∘ πy`
    have hηC : (πy ≫ g) C.genericPoint = P := hC.1.prop.2 (by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)
    by_cases hCy : πy C.genericPoint = y
    · refine ⟨Fin.last n, ?_⟩
      rw [Fin.snoc_last]
      have hCF : (C.support : Set (Y'y)) ⊆ F.support := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        refine closure_minimal (Set.singleton_subset_iff.mpr ((hFmem _).mpr hCy)) ?_
        exact F.idealSheaf.support.isClosed
      have hFirr : IsIrreducible (F.support : Set Y'y) := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact isIrreducible_singleton.closure
      have hFC := hC.1.2 ⟨hFirr, hsub F hFP⟩ hCF
      apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      exact C.eq_genericPoint_of_mem_support (hFC (by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl))
        F.coheight_genericPoint
    · have hV : πy C.genericPoint ∈ biregularLocus πy :=
        mem_biregularLocus_blowUpToBase_singleton hy hCy
      have hcoh : Order.coheight (πy C.genericPoint) = 1 := by
        rw [MMP.Positivity.coheight_map_of_mem_biregularLocus πy hV]
        exact C.coheight_genericPoint
      set D : Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh
      have hDη : Mori.PrimeDivisor.genericPoint D = πy C.genericPoint :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcoh
      have hDC : inverseTransformPrimeDivisor πy D = some C :=
        inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hDη.symm hV
      have hDexc : IsGermExceptionalCurve g P D := by
        refine ⟨maximal_support_of_subset hScl hSne D ?_,
          isCurveIn_idealSheaf_of_topologicalKrullDim_eq_two hYv hYd D⟩
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        refine closure_minimal (Set.singleton_subset_iff.mpr ?_) hScl
        change g (Mori.PrimeDivisor.genericPoint D) = P
        rw [hDη, ← Scheme.Hom.comp_apply, hηC]
      obtain ⟨j, hj⟩ := hE.exists_eq D hDexc
      refine ⟨j.castSucc, ?_⟩
      rw [Fin.snoc_castSucc]
      have := hE' j
      rw [hj, hDC] at this
      exact (Option.some.inj this).symm

omit [QuasiCompact (g ≫ sX)] [IsNormal Y] in
/-- A prime divisor of a surface germ `(X, P)` has its generic point in the open set over which a
resolution is an isomorphism, so it lies in the biregular locus. -/
theorem IsGermResolution.genericPoint_mem_biregularLocus (hg : IsGermResolution sX P g)
    (D : Mori.PrimeDivisor X) : D.genericPoint ∈ biregularLocus g := by
  obtain ⟨U, hU, hiso⟩ := hg.isIso_away
  refine le_biregularLocus (V := U) hiso ?_
  change D.genericPoint ∈ (U : Set X)
  rw [hU]
  intro h
  have h1 := D.coheight_genericPoint
  rw [h, coheight_eq_two_of_isClosed hg.isSurfaceGerm.1.1 hg.isSurfaceGerm.2.1
    hg.isSurfaceGerm.2.2.1] at h1
  exact absurd h1 (by decide)

/-- **Birational transforms along `g ∘ π`.** For a prime divisor `D` of `X`,
`(g ∘ π)⁻¹_* D = π⁻¹_* (g⁻¹_* D)`. -/
theorem IsGermResolution.inverseTransformPrimeDivisor_comp_blowUpToBase
    (hg : IsGermResolution sX P g) {y : Y} (hy : IsClosed ({y} : Set Y)) (hyP : g y = P)
    (D : Mori.PrimeDivisor X) :
    inverseTransformPrimeDivisor (πy ≫ g) D =
      (inverseTransformPrimeDivisor g D).bind (inverseTransformPrimeDivisor πy) := by
  obtain ⟨D₁, h₁, hη₁⟩ := exists_inverseTransformPrimeDivisor_eq_some D
    (hg.genericPoint_mem_biregularLocus D)
  have hD₁y : D₁.genericPoint ≠ y := by
    intro h
    have h1 := D.coheight_genericPoint
    rw [← hη₁, h, hyP, coheight_eq_two_of_isClosed hg.isSurfaceGerm.1.1 hg.isSurfaceGerm.2.1
      hg.isSurfaceGerm.2.2.1] at h1
    exact absurd h1 (by decide)
  obtain ⟨D₂, h₂, hη₂⟩ := exists_inverseTransformPrimeDivisor_eq_some D₁
    (mem_biregularLocus_blowUpToBase_singleton hy hD₁y)
  rw [h₁, Option.bind_some, h₂]
  have hη : (πy ≫ g) D₂.genericPoint = D.genericPoint := by
    rw [Scheme.Hom.comp_apply, hη₂, hη₁]
  exact inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hη
    (hη ▸ (hg.comp_blowUpToBase hy hyP).genericPoint_mem_biregularLocus D)

/-- **Birational transforms of divisors along `g ∘ π`**: `(g ∘ π)⁻¹_* B = π⁻¹_* (g⁻¹_* B)`. -/
theorem IsGermResolution.inverseTransformDivisor_comp_blowUpToBase {R : Type*} [AddCommMonoid R]
    (hg : IsGermResolution sX P g) {y : Y} (hy : IsClosed ({y} : Set Y)) (hyP : g y = P)
    (B : DivisorWithCoeffs R X) :
    inverseTransformDivisor (πy ≫ g) B =
      inverseTransformDivisor πy (inverseTransformDivisor g B) := by
  induction B using Finsupp.induction_linear with
  | zero => simp
  | add B₁ B₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]
  | single D r =>
    rw [inverseTransformDivisor_single, inverseTransformDivisor_single,
      hg.inverseTransformPrimeDivisor_comp_blowUpToBase hy hyP D]
    rcases inverseTransformPrimeDivisor g D with _ | D₁
    · simp
    · simp only [Option.bind_some, Option.elim_some]
      rw [inverseTransformDivisor_single]

end Blowup

/-! ### Intersection numbers on the blow-up -/

section Intersection

/-- If `f` is an isomorphism on the stalk at `x`, the residue field degree of `f` at `x` is `1`. -/
theorem residueFieldDegree_eq_one_of_isIso_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (h : IsIso (f.stalkMap x)) : residueFieldDegree f x = 1 := by
  unfold residueFieldDegree
  let _ := (f.residueFieldMap x).hom.toAlgebra
  have : IsIso (f.residueFieldMap x) :=
    ((IsLocalRing.ResidueField.mapEquiv
      (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv).toCommRingCatIso).isIso_hom
  have hbij : Function.Bijective (algebraMap (Y.residueField (f x)) (X.residueField x)) :=
    (asIso (f.residueFieldMap x)).commRingCatIsoToRingEquiv.bijective
  rw [← (AlgEquiv.ofBijective (Algebra.ofId _ _) hbij).toLinearEquiv.finrank_eq,
    Module.finrank_self]

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {P : X} {g : Y ⟶ X} [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]

open MMP.Threefold.Resolution

set_option hygiene false in
/-- The blow-up `π : Y' ⟶ Y` of the reduced closed point `y`. -/
local notation "πy" => blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds _))

set_option hygiene false in
/-- The blow-up `Y'` of the reduced closed point `y`. -/
local notation "Y'y" => blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds _))

/-- **Intersection numbers with a strict transform** (projection formula). Let `g` be a
resolution of `(X, P)`, `π` the blow-up of a closed point `y ∈ g⁻¹(P)`, `D` a divisor on `Y`
(Cartier, `Y` being smooth), `E` an exceptional curve of `g` and `E' = π⁻¹_* E`, an exceptional
curve of `g ∘ π`. Then `(π^* D · E') = (D · E)`. -/
theorem exists_isIntersectionNumber_pullback_inverseTransform (hg : IsGermResolution sX P g)
    {y : Y} (hy : IsClosed ({y} : Set Y)) (hyP : g y = P)
    [QuasiCompact ((πy ≫ g) ≫ sX)] [IsLocallyNoetherian Y'y] [IsNormal Y'y] [CompactSpace Y'y]
    (D : Divisor Y) {C : Mori.PrimeDivisor Y} (hC : IsGermExceptionalCurve g P C)
    {C' : Mori.PrimeDivisor Y'y} (hC'exc : IsGermExceptionalCurve (πy ≫ g) P C')
    (hC' : inverseTransformPrimeDivisor πy C = some C') :
    ∃ x : ℚ, IsIntersectionNumber (g ≫ sX) (Divisor.toQDivisor D) C.idealSheaf x ∧
      IsIntersectionNumber ((πy ≫ g) ≫ sX)
        (Divisor.toQDivisor (D.pullback (f := πy)
          (MMP.Fourfold.isCartier_of_isSmoothScheme hg.isSmoothResolution.isSmoothScheme D)
          (blowUpToBase_componentGenericPoint_notMem_supp hg.isVariety
            hg.topologicalKrullDim_eq hy D)))
        C'.idealSheaf x := by
  have hYv := hg.isVariety
  have hYs := hg.isSmoothResolution.isSmoothScheme
  have hg' := hg.comp_blowUpToBase hy hyP
  have hvar : Mori.IsVariety k ((πy ≫ g) ≫ sX) := by
    rw [Category.assoc]; exact isVariety_blowUp_singleton hYv hg.topologicalKrullDim_eq hy
  have : IsIntegral Y'y := hvar.toIsIntegral
  have : IsSeparated (g ≫ sX) := hYv.toIsSeparated
  have : LocallyOfFiniteType (g ≫ sX) := hYv.toLocallyOfFiniteType
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  have hD := MMP.Fourfold.isCartier_of_isSmoothScheme hYs D
  have hB := blowUpToBase_componentGenericPoint_notMem_supp hYv hg.topologicalKrullDim_eq hy D
  obtain ⟨E, hEpt, -⟩ := hC.exists_properCurve hg
  obtain ⟨E', hE'pt, -⟩ := hC'exc.exists_properCurve hg'
  obtain ⟨hmap, hV⟩ := map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hC'
  have hpt : πy E'.point = E.point := by rw [hE'pt, hmap, hEpt]
  have hproj := Divisor.degreeOn_pullback_eq_degree_pushforward (sY := g ≫ sX)
    (sX := (πy ≫ g) ≫ sX) πy (Category.assoc _ _ _).symm hD hB E'
  have hprop : IsProperCurve (g ≫ sX) (πy E'.point) := by rw [hpt]; exact E.isProperCurve
  have hres : residueFieldDegree πy E'.point = 1 :=
    residueFieldDegree_eq_one_of_isIso_stalkMap _ _
      (isIso_stalkMap_of_mem_biregularLocus πy (by rw [hE'pt]; exact hV))
  have hcurve : (⟨πy E'.point, hprop⟩ : ProperCurve (g ≫ sX)) = E := ProperCurve.ext hpt
  rw [OneCycle.pushforward_cycle, cyclePushforwardOfPoint] at hproj
  simp only [hprop, ↓reduceDIte] at hproj
  rw [hres, hcurve,
    OneCycle.degree_apply, Finsupp.sum_single_index (by simp), Nat.cast_one, one_mul] at hproj
  refine ⟨(D.degreeOn k (g ≫ sX) E.ι E.dim_le hD : ℚ), ?_, ?_⟩
  · have h := isIntersectionNumber_of_properCurve (Divisor.toQDivisor D)
      (QDivisor.isQCartier_toQDivisor hD) E C hEpt
    rwa [QDivisor.intersectionNumber_toQDivisor k _ _ _ D hD] at h
  · have hD' := hD.isCartier_pullback πy hB
    have h := isIntersectionNumber_of_properCurve (Divisor.toQDivisor (D.pullback hD hB))
      (QDivisor.isQCartier_toQDivisor hD') E' C' hE'pt
    rw [QDivisor.intersectionNumber_toQDivisor k _ _ _ _ hD', hproj] at h
    exact h

/-- **Intersection numbers with the exceptional curve.** With `π`, `F` as above and a divisor `D`
on `Y`, `(π^* D · F) = 0`: `π` contracts `F` to the point `y`. -/
theorem isIntersectionNumber_pullback_exceptional (hg : IsGermResolution sX P g)
    {y : Y} (hy : IsClosed ({y} : Set Y)) (hyP : g y = P)
    [QuasiCompact ((πy ≫ g) ≫ sX)] [IsLocallyNoetherian Y'y] [IsNormal Y'y] [CompactSpace Y'y]
    {F : Mori.PrimeDivisor Y'y}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
    (hFexc : IsGermExceptionalCurve (πy ≫ g) P F) (D : Divisor Y) :
    IsIntersectionNumber ((πy ≫ g) ≫ sX)
        (Divisor.toQDivisor (D.pullback (f := πy)
          (MMP.Fourfold.isCartier_of_isSmoothScheme hg.isSmoothResolution.isSmoothScheme D)
          (blowUpToBase_componentGenericPoint_notMem_supp hg.isVariety
            hg.topologicalKrullDim_eq hy D)))
        F.idealSheaf 0 := by
  have hYv := hg.isVariety
  have hYs := hg.isSmoothResolution.isSmoothScheme
  have hg' := hg.comp_blowUpToBase hy hyP
  have hvar : Mori.IsVariety k ((πy ≫ g) ≫ sX) := by
    rw [Category.assoc]; exact isVariety_blowUp_singleton hYv hg.topologicalKrullDim_eq hy
  have : IsIntegral Y'y := hvar.toIsIntegral
  have : IsSeparated (g ≫ sX) := hYv.toIsSeparated
  have : LocallyOfFiniteType (g ≫ sX) := hYv.toLocallyOfFiniteType
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  have hD := MMP.Fourfold.isCartier_of_isSmoothScheme hYs D
  have hB := blowUpToBase_componentGenericPoint_notMem_supp hYv hg.topologicalKrullDim_eq hy D
  obtain ⟨F', hF'pt, -⟩ := hFexc.exists_properCurve hg'
  have hFmem := mem_support_iff_of_idealSheaf_eq_exceptionalIdeal hy hF
  have hcon : F'.IsContractedBy πy := by
    intro q hq
    rw [hF'pt, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hq
    rw [(hFmem q).mp hq, hF'pt, (hFmem _).mp (by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)]
  have h0 := Divisor.degreeOn_pullback_eq_zero_of_isContractedBy (sY := g ≫ sX)
    (sX := (πy ≫ g) ≫ sX) πy (Category.assoc _ _ _).symm hD hB F' hcon
  have hD' := hD.isCartier_pullback πy hB
  have h := isIntersectionNumber_of_properCurve (Divisor.toQDivisor (D.pullback hD hB))
    (QDivisor.isQCartier_toQDivisor hD') F' F hF'pt
  rwa [QDivisor.intersectionNumber_toQDivisor k _ _ _ _ hD', h0, Int.cast_zero] at h

/-- The total transform `π^* C = π⁻¹_* C + (mult_y C) F` of a prime divisor, as a `ℚ`-divisor. -/
theorem toQDivisor_pullback_single (hg : IsGermResolution sX P g)
    {y : Y} (hy : IsClosed ({y} : Set Y))
    [IsLocallyNoetherian Y'y] [IsNormal Y'y] [CompactSpace Y'y]
    {F : Mori.PrimeDivisor Y'y}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
    (C : Mori.PrimeDivisor Y) :
    Divisor.toQDivisor (Divisor.pullback (f := πy) (Finsupp.single C 1 : Divisor Y)
          (MMP.Fourfold.isCartier_of_isSmoothScheme hg.isSmoothResolution.isSmoothScheme _)
          (blowUpToBase_componentGenericPoint_notMem_supp hg.isVariety
            hg.topologicalKrullDim_eq hy _)) =
      inverseTransformDivisor πy (Finsupp.single C (1 : ℚ)) +
        Finsupp.single F (DivisorWithCoeffs.multiplicityAt (Finsupp.single C (1 : ℚ)) y) := by
  rw [pullback_single_blowUp_singleton hg.isVariety hg.isSmoothResolution.isSmoothScheme
    hg.topologicalKrullDim_eq hy hF C, map_add, ← inverseTransformDivisor_toQDivisor,
    toQDivisor_single, toQDivisor_single, DivisorWithCoeffs.multiplicityAt_single]
  simp

omit [IsAlgClosed k] [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] in
/-- The total transform `π⁻¹_* D + (mult_y D) F` is `ℚ`-linear in `D`. -/
theorem smul_totalTransform_single {y : Y} (hy : IsClosed ({y} : Set Y))
    (F : Mori.PrimeDivisor Y'y) (G : Mori.PrimeDivisor Y) (q : ℚ) :
    q • (inverseTransformDivisor πy (Finsupp.single G (1 : ℚ)) +
        Finsupp.single F (DivisorWithCoeffs.multiplicityAt (Finsupp.single G (1 : ℚ)) y)) =
      inverseTransformDivisor πy (Finsupp.single G q) +
        Finsupp.single F (DivisorWithCoeffs.multiplicityAt (Finsupp.single G q) y) := by
  rw [smul_add, ← inverseTransformDivisorₗ_apply ℚ, ← LinearMap.map_smul,
    inverseTransformDivisorₗ_apply, Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul,
    mul_one, DivisorWithCoeffs.multiplicityAt_single, DivisorWithCoeffs.multiplicityAt_single,
    smul_eq_mul, nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_comm]

/-- **Intersection numbers of a total transform with a strict transform**: for every `ℚ`-divisor
`D` on `Y`, an exceptional curve `C` of `g` and `C' = π⁻¹_* C`,
`((π⁻¹_* D + (mult_y D) F) · C') = (D · C)`. -/
theorem exists_isIntersectionNumber_totalTransform (hg : IsGermResolution sX P g)
    {y : Y} (hy : IsClosed ({y} : Set Y)) (hyP : g y = P)
    [QuasiCompact ((πy ≫ g) ≫ sX)] [IsLocallyNoetherian Y'y] [IsNormal Y'y] [CompactSpace Y'y]
    {F : Mori.PrimeDivisor Y'y}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
    {C : Mori.PrimeDivisor Y} (hC : IsGermExceptionalCurve g P C)
    {C' : Mori.PrimeDivisor Y'y} (hC'exc : IsGermExceptionalCurve (πy ≫ g) P C')
    (hC' : inverseTransformPrimeDivisor πy C = some C') (D : QDivisor Y) :
    ∃ x : ℚ, IsIntersectionNumber (g ≫ sX) D C.idealSheaf x ∧
      IsIntersectionNumber ((πy ≫ g) ≫ sX)
        (inverseTransformDivisor πy D + Finsupp.single F (D.multiplicityAt y))
        C'.idealSheaf x := by
  have hYs := hg.isSmoothResolution.isSmoothScheme
  have hY's : IsSmoothScheme ((πy ≫ g) ≫ sX) :=
    (hg.comp_blowUpToBase hy hyP).isSmoothResolution.isSmoothScheme
  have hsingle : ∀ (G : Mori.PrimeDivisor Y) (q : ℚ), ∃ x : ℚ,
      IsIntersectionNumber (g ≫ sX) (Finsupp.single G q) C.idealSheaf x ∧
      IsIntersectionNumber ((πy ≫ g) ≫ sX)
        (inverseTransformDivisor πy (Finsupp.single G q) +
          Finsupp.single F (DivisorWithCoeffs.multiplicityAt (Finsupp.single G q) y))
        C'.idealSheaf x := by
    intro G q
    obtain ⟨x, h1, h2⟩ := exists_isIntersectionNumber_pullback_inverseTransform hg hy hyP
      (Finsupp.single G 1) hC hC'exc hC'
    rw [toQDivisor_pullback_single hg hy hF G] at h2
    rw [toQDivisor_single, Int.cast_one] at h1
    refine ⟨q * x, ?_, ?_⟩
    · have := h1.smul q (MMP.Fourfold.isQCartier_of_isSmoothScheme hYs _)
      rwa [Finsupp.smul_single, smul_eq_mul, mul_one] at this
    · have := h2.smul q (MMP.Fourfold.isQCartier_of_isSmoothScheme hY's _)
      rwa [smul_totalTransform_single] at this
  induction D using Finsupp.induction_linear with
  | zero =>
    obtain ⟨x, h1, h2⟩ := hsingle C 0
    simp only [Finsupp.single_zero, map_zero, zero_add] at h1 h2
    refine ⟨0, isIntersectionNumber_zero h1, ?_⟩
    simpa [DivisorWithCoeffs.multiplicityAt] using isIntersectionNumber_zero h2
  | add D₁ D₂ h₁ h₂ =>
    obtain ⟨x₁, h₁₁, h₁₂⟩ := h₁
    obtain ⟨x₂, h₂₁, h₂₂⟩ := h₂
    refine ⟨x₁ + x₂, isIntersectionNumber_add h₁₁ h₂₁, ?_⟩
    rw [map_add, DivisorWithCoeffs.multiplicityAt_add, Finsupp.single_add, add_add_add_comm]
    exact isIntersectionNumber_add h₁₂ h₂₂
  | single G q => exact hsingle G q

/-- **Intersection numbers of a total transform with the exceptional curve**: for every
`ℚ`-divisor `D` on `Y`, `((π⁻¹_* D + (mult_y D) F) · F) = 0`. -/
theorem isIntersectionNumber_totalTransform_exceptional (hg : IsGermResolution sX P g)
    {y : Y} (hy : IsClosed ({y} : Set Y)) (hyP : g y = P)
    [QuasiCompact ((πy ≫ g) ≫ sX)] [IsLocallyNoetherian Y'y] [IsNormal Y'y] [CompactSpace Y'y]
    {F : Mori.PrimeDivisor Y'y}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
    (hFexc : IsGermExceptionalCurve (πy ≫ g) P F) (D : QDivisor Y) :
    IsIntersectionNumber ((πy ≫ g) ≫ sX)
      (inverseTransformDivisor πy D + Finsupp.single F (D.multiplicityAt y)) F.idealSheaf 0 := by
  have hY's : IsSmoothScheme ((πy ≫ g) ≫ sX) :=
    (hg.comp_blowUpToBase hy hyP).isSmoothResolution.isSmoothScheme
  have hsingle : ∀ (G : Mori.PrimeDivisor Y) (q : ℚ),
      IsIntersectionNumber ((πy ≫ g) ≫ sX)
        (inverseTransformDivisor πy (Finsupp.single G q) +
          Finsupp.single F (DivisorWithCoeffs.multiplicityAt (Finsupp.single G q) y))
        F.idealSheaf 0 := by
    intro G q
    have h2 := isIntersectionNumber_pullback_exceptional hg hy hyP hF hFexc (Finsupp.single G 1)
    rw [toQDivisor_pullback_single hg hy hF G] at h2
    have := h2.smul q (MMP.Fourfold.isQCartier_of_isSmoothScheme hY's _)
    rwa [smul_totalTransform_single, mul_zero] at this
  induction D using Finsupp.induction_linear with
  | zero =>
    have h := isIntersectionNumber_zero
      (isIntersectionNumber_pullback_exceptional hg hy hyP hF hFexc 0)
    simpa [DivisorWithCoeffs.multiplicityAt] using h
  | add D₁ D₂ h₁ h₂ =>
    rw [map_add, DivisorWithCoeffs.multiplicityAt_add, Finsupp.single_add, add_add_add_comm,
      ← add_zero (0 : ℚ)]
    exact isIntersectionNumber_add h₁ h₂
  | single G q => exact hsingle G q

end Intersection

/-! ### The log discrepancy vector after blowing up a point -/

section LogDiscrepancy

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {P : X} {B : QDivisor X} {g : Y ⟶ X} [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y]
  [IsNormal Y] {n : ℕ} {E : Fin n → Mori.PrimeDivisor Y} {a : Fin n → ℚ}

open MMP.Threefold.Resolution

set_option hygiene false in
/-- The blow-up `π : Y' ⟶ Y` of the reduced closed point `y`. -/
local notation "πy" => blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds _))

set_option hygiene false in
/-- The blow-up `Y'` of the reduced closed point `y`. -/
local notation "Y'y" => blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds _))

/-- **The log discrepancy vector after blowing up a point, given `K_{Y'} = π^* K_Y + F`.** Let
`a` be the log discrepancy vector of `(X, P; B)` on a resolution `g` with exceptional curves
`E_1, …, E_n`, `π : Y' ⟶ Y` the blow-up of a closed point `y ∈ g⁻¹(P)` with exceptional curve
`F`, `E'_j = π⁻¹_* E_j`, and `K_Y` a canonical divisor of `Y` such that `π^* K_Y + F` is a
canonical divisor of `Y'`. Then `(a_1, …, a_n, 2 - mult_y Θ_{g,a})` is the log discrepancy vector
of `(X, P; B)` on `g ∘ π` with exceptional curves `E'_1, …, E'_n, F`. -/
theorem isGermLogDiscrepancyVector_snoc_blowUp_of_isCanonicalDivisor
    (ha : IsGermLogDiscrepancyVector sX P B g E a) {y : Y} (hy : IsClosed ({y} : Set Y))
    (hyP : g y = P)
    [QuasiCompact ((πy ≫ g) ≫ sX)] [IsLocallyNoetherian Y'y] [IsNormal Y'y] [CompactSpace Y'y]
    {F : Mori.PrimeDivisor Y'y}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
    {E' : Fin n → Mori.PrimeDivisor Y'y}
    (hE' : ∀ j, inverseTransformPrimeDivisor πy (E j) = some (E' j))
    {K : Divisor Y} (hK : K.IsCanonicalDivisor (g ≫ sX) 2)
    (hK' : (Divisor.pullback (f := πy) K
        (MMP.Fourfold.isCartier_of_isSmoothScheme ha.2.1.isSmoothResolution.isSmoothScheme K)
        (blowUpToBase_componentGenericPoint_notMem_supp ha.2.1.isVariety
          ha.2.1.topologicalKrullDim_eq hy K) +
        Finsupp.single F 1).IsCanonicalDivisor ((πy ≫ g) ≫ sX) 2) :
    IsGermLogDiscrepancyVector sX P B (πy ≫ g) (Fin.snoc E' F : Fin (n + 1) → _)
      (Fin.snoc a (2 - (logPullbackBoundary g B E a).multiplicityAt y) : Fin (n + 1) → ℚ) := by
  have hΘ := ((isGermLogDiscrepancyVector_iff sX P B g E a).mp ha).2.2.2 K hK
  have hBg := ha.1
  have hg := ha.2.1
  have hg' := hg.comp_blowUpToBase hy hyP
  have hE := ha.2.2.1
  have hE'e := hE.snoc_blowUp hg hy hyP hF hE'
  rw [isGermLogDiscrepancyVector_iff_of_isCanonicalDivisor hK']
  refine ⟨hBg, hg', hE'e, fun i => ?_⟩
  set Θ := logPullbackBoundary g B E a with hΘdef
  have hΘ' : inverseTransformDivisor πy Θ = inverseTransformDivisor πy
      (inverseTransformDivisor g B) + ∑ j, Finsupp.single (E' j) (1 - a j) := by
    rw [hΘdef, logPullbackBoundary, map_add, map_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => inverseTransformDivisor_single_of_eq_some (hE' j) _
  have hT : Divisor.toQDivisor (Divisor.pullback (f := πy) K
        (MMP.Fourfold.isCartier_of_isSmoothScheme hg.isSmoothResolution.isSmoothScheme K)
        (blowUpToBase_componentGenericPoint_notMem_supp hg.isVariety
          hg.topologicalKrullDim_eq hy K) + Finsupp.single F 1) +
      inverseTransformDivisor (πy ≫ g) B +
      ∑ j, Finsupp.single ((Fin.snoc E' F : Fin (n + 1) → _) j)
        (1 - (Fin.snoc a (2 - Θ.multiplicityAt y) : Fin (n + 1) → ℚ) j) =
      inverseTransformDivisor πy (Divisor.toQDivisor K + Θ) +
        Finsupp.single F ((Divisor.toQDivisor K + Θ).multiplicityAt y) := by
    rw [Divisor.IsPullback.pullback_eq _ (isPullback_blowUp_singleton hg.isVariety
      hg.isSmoothResolution.isSmoothScheme hg.topologicalKrullDim_eq hy hF K _),
      hg.inverseTransformDivisor_comp_blowUpToBase hy hyP, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [map_add (inverseTransformDivisor πy) (Divisor.toQDivisor K) Θ, hΘ',
      DivisorWithCoeffs.multiplicityAt_add, multiplicityAt_toQDivisor,
      inverseTransformDivisor_toQDivisor, map_add Divisor.toQDivisor, map_add Divisor.toQDivisor,
      toQDivisor_single, toQDivisor_single,
      show ((K.multiplicityAt y : ℤ) : ℚ) + Θ.multiplicityAt y =
        ((K.multiplicityAt y : ℤ) : ℚ) + ((1 : ℤ) : ℚ) + (1 - (2 - Θ.multiplicityAt y)) by
          push_cast; ring,
      Finsupp.single_add, Finsupp.single_add]
    abel
  rw [hT]
  induction i using Fin.lastCases with
  | last =>
    rw [Fin.snoc_last]
    have hFexc := hE'e.isGermExceptionalCurve (Fin.last n)
    rw [Fin.snoc_last] at hFexc
    exact isIntersectionNumber_totalTransform_exceptional hg hy hyP hF hFexc _
  | cast j =>
    rw [Fin.snoc_castSucc]
    have hexc := hE'e.isGermExceptionalCurve j.castSucc
    rw [Fin.snoc_castSucc] at hexc
    obtain ⟨x, h1, h2⟩ := exists_isIntersectionNumber_totalTransform hg hy hyP hF
      (hE.isGermExceptionalCurve j) hexc (hE' j) (Divisor.toQDivisor K + Θ)
    rw [h1.unique (hΘ j)] at h2
    exact h2

omit [IsAlgClosed k] [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] in
/-- Being a canonical divisor depends only on the structure morphism, not on how it is written. -/
theorem isCanonicalDivisor_of_eq {Z : Scheme.{u}} [IsLocallyNoetherian Z] [IsNormal Z]
    {f f' : Z ⟶ Spec (.of k)} (h : f = f')
    {K : Divisor Z} {d : ℕ} (hK : K.IsCanonicalDivisor f d) : K.IsCanonicalDivisor f' d := by
  subst h; exact hK

omit [IsAlgClosed k] [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] in
/-- The source of a resolution of `(X, P)` is quasi-compact over `k`. -/
theorem IsGermResolution.quasiCompact_comp (hg : IsGermResolution sX P g) :
    QuasiCompact (g ≫ sX) := by
  have := hg.isSmoothResolution.isProper
  have : QuasiCompact sX := hg.isSurfaceGerm.1.1.toQuasiCompact
  infer_instance

/-- **The log discrepancy vector after blowing up a point** (in the proofs of FA 3.1.4, 3.1.5,
3.3.2), given the canonical divisor of the blow-up. Let `g : Y ⟶ X` be a resolution of `(X, P)`
with exceptional curves `E_1, …, E_n` and log discrepancy vector `a`, `y ∈ g⁻¹(P)` a closed
point, `π : Y' ⟶ Y` the blow-up of `y` and `F = π⁻¹(y)_red`. Suppose that `π^* K_Y + F` is a
canonical divisor of `Y'` for every canonical divisor `K_Y` of `Y`. Then `g ∘ π` is a resolution
of `(X, P)` whose exceptional curves are the birational transforms `E'_j = π⁻¹_* E_j` and `F`,
and its log discrepancy vector `a'` is `a'_{E'_j} = a_j`, `a'_F = 2 - mult_y Θ_{g,a}`. -/
theorem isGermLogDiscrepancyVector_snoc_blowUp_iff_of_isCanonicalDivisor
    (ha : IsGermLogDiscrepancyVector sX P B g E a) {y : Y} (hy : IsClosed ({y} : Set Y))
    (hyP : g y = P) {F : Mori.PrimeDivisor Y'y}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
    (hcan :
      haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
        (isSmoothScheme_blowUp_singleton ha.2.1.isVariety ha.2.1.isSmoothResolution.isSmoothScheme
          ha.2.1.topologicalKrullDim_eq hy)).1
      haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
        (isSmoothScheme_blowUp_singleton ha.2.1.isVariety ha.2.1.isSmoothResolution.isSmoothScheme
          ha.2.1.topologicalKrullDim_eq hy)).2
      haveI := compactSpace_blowUp_singleton ha.2.1.isVariety ha.2.1.topologicalKrullDim_eq hy
      ∀ K : Divisor Y, K.IsCanonicalDivisor (g ≫ sX) 2 →
        (Divisor.pullback (f := πy) K
          (MMP.Fourfold.isCartier_of_isSmoothScheme ha.2.1.isSmoothResolution.isSmoothScheme K)
          (blowUpToBase_componentGenericPoint_notMem_supp ha.2.1.isVariety
            ha.2.1.topologicalKrullDim_eq hy K) +
          Finsupp.single F 1).IsCanonicalDivisor (πy ≫ g ≫ sX) 2) :
    haveI := (ha.2.1.comp_blowUpToBase hy hyP).quasiCompact_comp
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
      (ha.2.1.comp_blowUpToBase hy hyP).isSmoothResolution.isSmoothScheme).1
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
      (ha.2.1.comp_blowUpToBase hy hyP).isSmoothResolution.isSmoothScheme).2
    IsGermResolution sX P (πy ≫ g) ∧
      ∃ E' : Fin n → Mori.PrimeDivisor Y'y,
        (∀ j, inverseTransformPrimeDivisor πy (E j) = some (E' j)) ∧
        IsExceptionalCurveEnumeration (πy ≫ g) P (Fin.snoc E' F : Fin (n + 1) → _) ∧
        ∀ a' : Fin (n + 1) → ℚ,
          IsGermLogDiscrepancyVector sX P B (πy ≫ g) (Fin.snoc E' F : Fin (n + 1) → _) a' ↔
            a' = (Fin.snoc a (2 - (logPullbackBoundary g B E a).multiplicityAt y) :
              Fin (n + 1) → ℚ) := by
  have hg := ha.2.1
  have hYv := hg.isVariety
  have hYs := hg.isSmoothResolution.isSmoothScheme
  have hYd := hg.topologicalKrullDim_eq
  have hg' := hg.comp_blowUpToBase hy hyP
  have := hg'.quasiCompact_comp
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
    hg'.isSmoothResolution.isSmoothScheme).1
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
    hg'.isSmoothResolution.isSmoothScheme).2
  have := compactSpace_blowUp_singleton hYv hYd hy
  have hcoh2 : Order.coheight y = 2 := coheight_eq_two_of_isClosed hYv hYd hy
  have hex : ∀ j, ∃ E'' : Mori.PrimeDivisor Y'y,
      inverseTransformPrimeDivisor πy (E j) = some E'' := fun j => by
    refine (exists_inverseTransformPrimeDivisor_eq_some (E j)
      (mem_biregularLocus_blowUpToBase_singleton hy fun h => ?_)).imp fun _ h => h.1
    have := (E j).coheight_genericPoint
    rw [h, hcoh2] at this
    exact absurd this (by decide)
  choose E' hE' using hex
  have hE'e := ha.2.2.1.snoc_blowUp hg hy hyP hF hE'
  have := hg.isIntegral sX
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  have hdim : topologicalKrullDim Y = ((2 : ℕ) : WithBot ℕ∞) := hYd
  obtain ⟨K, hK⟩ := @exists_isCanonicalDivisor_of_isSmoothScheme Y _ _ _ _ k _ (g ≫ sX) hYv
    hYs 2 hdim
  have hK' := isCanonicalDivisor_of_eq (k := k) (Category.assoc _ _ _).symm (hcan K hK)
  have hv := isGermLogDiscrepancyVector_snoc_blowUp_of_isCanonicalDivisor ha hy hyP hF hE' hK hK'
  refine ⟨hg', E', hE', hE'e, fun a' => ⟨fun h => ?_, fun h => h ▸ hv⟩⟩
  exact (existsUnique_isGermLogDiscrepancyVector ha.1 hg' hE'e).unique h hv

end LogDiscrepancy

end MMP.Flips
