module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.PairClasses
public import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
public import MMP.AlgebraicGeometry.Singularities.Basic
import MMP.AlgebraicGeometry.Singularities.Surface.NoetherFormulaLcObstruction
import MMP.AlgebraicGeometry.Singularities.Surface.WeightedDualGraph
import MMP.AlgebraicGeometry.Intersection.Surface.BlowupGenusDropAdjunction
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafCoherent
import MMP.AlgebraicGeometry.Singularities.Surface.DualGraphBoundaryDegree

/-!
# A single exceptional curve with `β = 2` and a tangency or a triple point is not lc

Let `(X, P; B)` be a surface germ with reduced boundary and `f : Y ⟶ X` its minimal resolution.
Suppose that `Γ(f)` is a rational tree with a single vertex `v_1` and boundary degree
`β_1 = 2`. If the extended dual graph `Γ^*(f)` does not consist of `v_1` and exactly two
boundary points `(C_1, y_1)`, `(C_2, y_2)` with `y_1 ≠ y_2`, each joined to `v_1` by an edge of
weight `1`, then `(X, B)` is not log canonical near `P`.

## Main results

* `MMP.Flips.IsExtendedDualGraph.not_isLogCanonical_of_boundary_eq_two`.

## Implementation notes

The single exceptional curve is `E : Fin 1 → Mori.PrimeDivisor Y`, and the boundary points of
`f` are enumerated (each exactly once) by `pt : Fin m → Mori.PrimeDivisor Y × Y`, as in
`MMP.Flips.IsExtendedDualGraph`. "`Γ^*(f)` consists of `v_1` and exactly two boundary points
with distinct points, each joined to `v_1` by an edge of weight `1`" is: there are two distinct
indices `l₁ ≠ l₂` exhausting `Fin m`, with `y_{l₁} ≠ y_{l₂}` and both edge weights to `v_1`
equal to `1`; this does not depend on the enumeration. "`(X, B)` is log canonical near `P`" is
spelled as in `MMP.Flips.IsGermLogDiscrepancyVector.not_isLogCanonical_of_two_lt_multiplicityAt`:
on some open neighbourhood `U` of `P`, `(U, B|_U)` is log canonical with canonical divisor
`K_X|_U`, for a canonical divisor `K_X` of `X`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], (3.3.2)
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Flips

open MMP.Mori

/-- In a Noetherian space every point `y` of a closed set `F` lies on a maximal irreducible
subset `Z` of `F`, and `F ⊆ Z ∪ C` for a closed set `C` not containing `Z`. -/
private lemma exists_maximal_isIrreducible_subset {T : Type*} [TopologicalSpace T]
    [TopologicalSpace.NoetherianSpace T] {F : Set T} (hF : IsClosed F) {y : T} (hy : y ∈ F) :
    ∃ Z C : Set T, Maximal (fun W : Set T => IsIrreducible W ∧ W ⊆ F) Z ∧ IsClosed Z ∧ y ∈ Z ∧
      IsClosed C ∧ F ⊆ Z ∪ C ∧ ¬ Z ⊆ C := by
  obtain ⟨S, hSfin, hScl, hSirr, hSeq⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hF
  obtain ⟨T₀, hT₀, hyT₀⟩ : y ∈ ⋃₀ S := hSeq ▸ hy
  obtain ⟨Z, hT₀Z, hZ⟩ := hSfin.exists_le_maximal hT₀
  have hZS : Z ∈ S := hZ.prop
  have hZF : Z ⊆ F := hSeq ▸ Set.subset_sUnion_of_mem hZS
  have hsub : ∀ {W : Set T}, IsIrreducible W → ∀ {S' : Set (Set T)}, S' ⊆ S →
      W ⊆ ⋃₀ S' → ∃ t ∈ S', W ⊆ t := by
    intro W hW S' hS' hWS
    have hfin : S'.Finite := hSfin.subset hS'
    obtain ⟨t, ht, hWt⟩ := (isIrreducible_iff_sUnion_isClosed.mp hW) hfin.toFinset
      (fun t ht => hScl t (hS' (hfin.mem_toFinset.mp ht))) (by simpa using hWS)
    exact ⟨t, hfin.mem_toFinset.mp ht, hWt⟩
  have hmax : Maximal (fun W : Set T => IsIrreducible W ∧ W ⊆ F) Z := by
    refine ⟨⟨hSirr Z hZS, hZF⟩, fun W hW hZW => ?_⟩
    obtain ⟨t, htS, hWt⟩ := hsub hW.1 le_rfl (hSeq ▸ hW.2)
    exact (hZ.2 htS (hZW.trans hWt)).trans' hWt
  refine ⟨Z, ⋃₀ (S \ {Z}), hmax, hScl Z hZS, hT₀Z hyT₀,
    (hSfin.subset Set.sdiff_subset).isClosed_sUnion fun t ht => hScl t ht.1, ?_, ?_⟩
  · intro x hx
    obtain ⟨t, htS, hxt⟩ := (hSeq ▸ hx : x ∈ ⋃₀ S)
    by_cases htZ : t = Z
    · exact Or.inl (htZ ▸ hxt)
    · exact Or.inr ⟨t, ⟨htS, htZ⟩, hxt⟩
  · intro hZC
    obtain ⟨t, ⟨htS, htZ⟩, hZt⟩ := hsub (hSirr Z hZS) Set.sdiff_subset hZC
    exact htZ (le_antisymm (hZ.2 htS hZt) hZt)

/-- A prime divisor in the support of `mapPrimeDivisors φ D` is `φ` of some prime divisor. -/
private theorem exists_eq_some_of_mem_support_mapPrimeDivisors {X Y : Scheme.{u}} {R : Type*}
    [AddCommMonoid R] {φ : Mori.PrimeDivisor X → Option (Mori.PrimeDivisor Y)}
    {D : DivisorWithCoeffs R X} {Q : Mori.PrimeDivisor Y}
    (hQ : Q ∈ (DivisorWithCoeffs.mapPrimeDivisors φ D).support) : ∃ E, φ E = some Q := by
  by_contra! h
  exact Finsupp.mem_support_iff.mp hQ (mapPrimeDivisors_apply_eq_zero_of_forall_ne h D)

/-- The coefficient of `g⁻¹_*(D)` in `g⁻¹_* B` is that of `D` in `B`. -/
private theorem inverseTransformDivisor_apply_of_eq_some {X Y : Scheme.{u}} {R : Type*}
    [AddCommMonoid R] {g : Y ⟶ X} {D : Mori.PrimeDivisor X} {C : Mori.PrimeDivisor Y}
    (hD : inverseTransformPrimeDivisor g D = some C) (B : DivisorWithCoeffs R X) :
    inverseTransformDivisor g B C = B D :=
  MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hD (fun _ hD' =>
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
        hD').1.symm.trans
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hD).1) B

section DualGraph

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {P : X} {B : QDivisor X} {f : Y ⟶ X} [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y]
    [IsNormal Y] {n : ℕ} {E : Fin n → Mori.PrimeDivisor Y} {Γ : WeightedGraph (Fin n)}

/-- If the fibre `f⁻¹(P)` is preconnected and there is at least one exceptional curve, then
every point of `f⁻¹(P)` lies on an exceptional curve. -/
private lemma exists_mem_support_of_isPreconnected (hΓ : IsWeightedDualGraph sX P B f E Γ)
    (hconn : _root_.IsPreconnected (f.base ⁻¹' {P})) (u : Fin n) {y : Y} (hy : f y = P) :
    ∃ j, y ∈ (E j).support := by
  have hg := hΓ.isGermResolution
  have hE := hΓ.isExceptionalCurveEnumeration
  have hYv := hg.isVariety
  have : IsIntegral Y := hYv.toIsIntegral
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  have : IsNoetherian Y := {}
  have hP : IsClosed ({P} : Set X) := hg.isSurfaceGerm.2.2.1
  have hFcl : IsClosed (f.base ⁻¹' {P}) := hP.preimage f.base.hom.continuous
  obtain ⟨Z, C, hZ, hZcl, hyZ, hCcl, hFZC, hZC⟩ := exists_maximal_isIrreducible_subset hFcl hy
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hZ.prop.1 hZcl
  have hξZ : ξ ∈ Z := hξ.mem
  have hEuF : ((E u).support : Set Y) ⊆ f.base ⁻¹' {P} :=
    (hE.isGermExceptionalCurve u).1.prop.2
  have hξncl : ¬ IsClosed ({ξ} : Set Y) := by
    intro hcl
    have hZξ : Z = {ξ} := by rw [← hξ.def, hcl.closure_eq]
    have hξC : ξ ∉ C := fun h => hZC (hZξ ▸ Set.singleton_subset_iff.mpr h)
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hconn {ξ} C hcl hCcl
        (hZξ ▸ hFZC) (by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
            iff_false, not_and]
          rintro - rfl
          exact hξC) with h | h
    · exact (hE.isGermExceptionalCurve u).2.not_subsingleton
        ((Set.subsingleton_singleton).anti (hEuF.trans h))
    · exact hξC (h (hZ.prop.2 hξZ))
  obtain ⟨c, hcZ, hccl⟩ := hZcl.exists_closed_singleton ⟨ξ, hξZ⟩
  have hcξ : c ≠ ξ := fun h => hξncl (h ▸ hccl)
  have hξc : ξ ⤳ c := hξ.specializes hcZ
  have hco2 := MMP.Threefold.Resolution.coheight_eq_two_of_isClosed hYv
    hg.topologicalKrullDim_eq hccl
  have hξmax : ¬ IsMax ξ := by
    intro hmax
    have : IsIntegral X := hg.isSurfaceGerm.1.1.toIsIntegral
    have := hg.isSmoothResolution.isBirationalMorphism.isDominant
    have h2 : ξ ⤳ genericPoint Y := hmax (genericPoint_specializes ξ)
    have hgη : f (genericPoint Y) = P := hZ.prop.2 (h2.mem_closed hZcl hξZ)
    rw [map_genericPoint_of_isDominant] at hgη
    have : Subsingleton X := ⟨fun a b => by
      have ha := (genericPoint_specializes a).mem_closed hP (Set.mem_singleton_iff.mpr hgη)
      have hb := (genericPoint_specializes b).mem_closed hP (Set.mem_singleton_iff.mpr hgη)
      rw [Set.mem_singleton_iff] at ha hb
      rw [ha, hb]⟩
    have h0 := topologicalKrullDim_zero_of_discreteTopology X
    rw [hg.isSurfaceGerm.2.1] at h0
    exact absurd h0 (by decide)
  have hco : Order.coheight ξ = 1 := by
    have hcξlt : c < ξ := lt_of_le_not_ge hξc fun h =>
      hcξ ((h : c ⤳ ξ).mem_closed hccl rfl).symm
    have hlt : Order.coheight ξ < 2 := hco2 ▸ Order.coheight_strictAnti hcξlt
      (lt_of_le_of_lt (hco2 ▸ Order.coheight_anti hcξlt.le) (by decide))
    have hne : Order.coheight ξ ≠ 0 := fun h => hξmax (Order.coheight_eq_zero.mp h)
    generalize Order.coheight ξ = d at hlt hne ⊢
    induction d using ENat.recTopCoe with
    | top => exact absurd hlt (by decide)
    | coe d =>
      norm_cast at hlt hne ⊢
      omega
  let D : Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne ξ hco
  have hDsupp : (D.support : Set Y) = Z := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne, hξ.def]
  obtain ⟨j, hj⟩ := hE.exists_eq D ⟨hDsupp ▸ hZ,
    isCurveIn_idealSheaf_of_topologicalKrullDim_eq_two hYv hg.topologicalKrullDim_eq D⟩
  exact ⟨j, by rwa [hj, hDsupp]⟩

omit [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] in
/-- A component of `f⁻¹_* B` does not lie over the closed point `P` of a surface germ. -/
private theorem map_genericPoint_ne_of_mem_support (hX : IsSurfaceGerm sX P)
    {C : Mori.PrimeDivisor Y} (hC : C ∈ (inverseTransformDivisor f B).support) :
    f.base C.genericPoint ≠ P := by
  intro hP
  obtain ⟨D, hD⟩ := exists_eq_some_of_mem_support_mapPrimeDivisors hC
  have h := MMP.Positivity.coheight_map_of_mem_biregularLocus f
    (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hD).2
  rw [hP, MMP.Threefold.Resolution.coheight_eq_two_of_isClosed hX.1.1 hX.2.1 hX.2.2.1,
    C.coheight_genericPoint] at h
  exact absurd h (by decide)

omit [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] in
/-- The components of `f⁻¹_* B` have nonnegative coefficients and are not exceptional curves. -/
private theorem nonneg_and_ne_of_mem_support_inverseTransformDivisor
    (hg : IsGermResolution sX P f) (hB : IsSurfaceGermWithBoundary sX P B)
    {E C : Mori.PrimeDivisor Y} (hE : IsGermExceptionalCurve f P E)
    (hC : C ∈ (inverseTransformDivisor f B).support) :
    0 ≤ inverseTransformDivisor f B C ∧ E ≠ C := by
  obtain ⟨D, hD⟩ := exists_eq_some_of_mem_support_mapPrimeDivisors hC
  refine ⟨inverseTransformDivisor_apply_of_eq_some hD B ▸ (hB.2.2 D).1, fun hEC => ?_⟩
  refine map_genericPoint_ne_of_mem_support hg.isSurfaceGerm hC <| hE.1.prop.2 ?_
  rw [hEC, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure rfl

omit [IsLocallyNoetherian Y] [IsNormal Y] in
private theorem logPullbackBoundary_zero_apply (E : Fin 1 → Mori.PrimeDivisor Y)
    (D : Mori.PrimeDivisor Y) :
    logPullbackBoundary f B E 0 D = inverseTransformDivisor f B D + Finsupp.single (E 0) 1 D := by
  simp [logPullbackBoundary]

omit [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] in
private theorem logPullbackBoundary_zero_apply_of_mem_support
    (hg : IsGermResolution sX P f) (hB : IsSurfaceGermWithBoundary sX P B)
    (hred : IsReducedBoundary B) {E : Fin 1 → Mori.PrimeDivisor Y}
    (hE : IsGermExceptionalCurve f P (E 0)) {C : Mori.PrimeDivisor Y}
    (hC : C ∈ (inverseTransformDivisor f B).support) :
    logPullbackBoundary f B E 0 C = 1 ∧ E 0 ≠ C := by
  have hne := (nonneg_and_ne_of_mem_support_inverseTransformDivisor hg hB hE hC).2
  refine ⟨?_, hne⟩
  obtain ⟨D, hD⟩ := exists_eq_some_of_mem_support_mapPrimeDivisors hC
  have hCD := inverseTransformDivisor_apply_of_eq_some hD B
  have hDB : D ∈ B.support := by
    rw [Finsupp.mem_support_iff, ← hCD]
    exact Finsupp.mem_support_iff.mp hC
  rw [logPullbackBoundary_zero_apply, hCD, hred D hDB, Finsupp.single_eq_of_ne hne.symm, add_zero]

omit [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] in
private theorem logPullbackBoundary_zero_apply_self
    (hg : IsGermResolution sX P f) (hB : IsSurfaceGermWithBoundary sX P B)
    {E : Fin 1 → Mori.PrimeDivisor Y} (hE : IsGermExceptionalCurve f P (E 0)) :
    logPullbackBoundary f B E 0 (E 0) = 1 := by
  rw [logPullbackBoundary_zero_apply, Finsupp.notMem_support_iff.mp fun h =>
    (nonneg_and_ne_of_mem_support_inverseTransformDivisor hg hB hE h).2 rfl,
    Finsupp.single_eq_same, zero_add]

omit [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] in
private theorem logPullbackBoundary_zero_nonneg
    (hg : IsGermResolution sX P f) (hB : IsSurfaceGermWithBoundary sX P B)
    {E : Fin 1 → Mori.PrimeDivisor Y} (hE : IsGermExceptionalCurve f P (E 0))
    (D : Mori.PrimeDivisor Y) : 0 ≤ logPullbackBoundary f B E 0 D := by
  rw [logPullbackBoundary_zero_apply]
  refine add_nonneg ?_ ?_
  · by_cases hD : D ∈ (inverseTransformDivisor f B).support
    · exact (nonneg_and_ne_of_mem_support_inverseTransformDivisor hg hB hE hD).1
    · rw [Finsupp.notMem_support_iff.mp hD]
  · classical
    rw [Finsupp.single_apply]
    split_ifs <;> norm_num

/-- For a single exceptional curve forming a rational tree with `β_1 = 2`, the log discrepancy
vector is `0`. -/
private theorem isGermLogDiscrepancyVector_zero_of_boundary_eq_two
    {E : Fin 1 → Mori.PrimeDivisor Y} {Γ : WeightedGraph (Fin 1)}
    (hW : IsWeightedDualGraph sX P B f E Γ) (hΓ : Γ.IsRationalTree) (hβ : Γ.boundary 0 = 2) :
    IsGermLogDiscrepancyVector sX P B f E 0 := by
  refine (hW.isGermLogDiscrepancyVector_iff 0).mpr <|
    (WeightedGraph.isLogDiscrepancyVector_iff_eq_zero_of_isChainOrder hΓ hW.isNegDef one_pos
      (e := Equiv.refl _) ⟨fun i => hΓ.genus_eq_zero _, fun i j => ?_⟩ fun i => ?_).mpr rfl
  · fin_cases i
    fin_cases j
    simp [Γ.edgeWeight_self]
  · fin_cases i
    norm_num [hβ]

/-- With a single exceptional curve `E_1`, every boundary point lies on `E_1`. -/
private theorem mem_support_of_isExtendedDualGraph {m : ℕ} {E : Fin 1 → Mori.PrimeDivisor Y}
    {pt : Fin m → Mori.PrimeDivisor Y × Y} {Γ : ExtendedWeightedGraph (Fin 1) (Fin m)}
    (h : IsExtendedDualGraph sX P B f E pt Γ) (l : Fin m) : (pt l).2 ∈ (E 0).support := by
  have hg := h.isWeightedDualGraph.isGermResolution
  have : IsIntegral Y := hg.isVariety.toIsIntegral
  have : IsProper f := hg.isSmoothResolution.isProper
  have hconn := ((MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
    (f ≫ sX) sX hg.isVariety hg.isSurfaceGerm.1 f
    hg.isSmoothResolution.isBirationalMorphism).2 P).isPreconnected
  obtain ⟨j, hj⟩ := exists_mem_support_of_isPreconnected h.isWeightedDualGraph hconn 0
    (h.isGermBoundaryPoint l).2.2
  rwa [Subsingleton.elim j 0] at hj

end DualGraph

open MMP.Threefold.Resolution MMP.Resolution in
/-- A point common to two distinct prime divisors of a surface is a closed point. -/
private theorem isClosed_singleton_of_mem_inter {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] (hdim : topologicalKrullDim X = 2) {C D : Mori.PrimeDivisor X} (hCD : C ≠ D)
    {y : X} (hy : y ∈ C.support ∩ D.support) : IsClosed ({y} : Set X) := by
  have hne : y ≠ C.genericPoint := by
    rintro rfl
    exact hCD (MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support D C hy.2).symm
  have hle : y ≤ C.genericPoint := by
    have h := hy.1
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h
    exact specializes_iff_mem_closure.mpr h
  have hlt : y < C.genericPoint := lt_of_le_not_ge hle fun h =>
    hne (Specializes.antisymm (show y ⤳ C.genericPoint from h)
      (show C.genericPoint ⤳ y from hle)).eq
  have h2 := Order.coheight_add_one_le hlt
  rw [Mori.PrimeDivisor.coheight_genericPoint] at h2
  refine closure_subset_iff_isClosed.mp fun w hw => ?_
  have hwy : w ≤ y := specializes_iff_mem_closure.mpr hw
  by_contra hne
  have hlt' : w < y := lt_of_le_not_ge hwy fun h => hne (Specializes.antisymm
    (show w ⤳ y from h) (show y ⤳ w from hwy)).eq
  have h4 := Order.coheight_add_one_le hlt'
  have h5 := coheight_le_topologicalKrullDim w
  rw [hdim] at h5
  have h6 : (1 : ℕ∞) + 1 + 1 ≤ 2 :=
    (add_le_add h2 (le_refl (1 : ℕ∞))).trans (h4.trans (WithBot.coe_le_coe.mp h5))
  exact absurd h6 (by decide)

/-- On a smooth variety a prime divisor has multiplicity at least one at each of its points. -/
private theorem one_le_toNat_multiplicityAt {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of k)} (hsm : IsSmoothScheme sY)
    (D : Mori.PrimeDivisor Y) {y : Y} (hy : y ∈ D.support) : 1 ≤ (D.multiplicityAt y).toNat := by
  have htop := MMP.Threefold.Resolution.multiplicityAt_ne_top D
    (MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm D) y
  have h1 : (1 : ℕ∞) ≤ D.multiplicityAt y := by
    refine le_iSup₂_of_le (f := fun (m : ℕ) (_ : D.idealSheaf.stalkIdeal y ≤
      IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ m) => (m : ℕ∞)) 1 ?_ (by simp)
    rw [pow_one]
    exact IsLocalRing.le_maximalIdeal
      ((Scheme.IdealSheafData.stalkIdeal_eq_top_iff _).not.mpr (not_not.mpr hy))
  lift D.multiplicityAt y to ℕ using htop with m
  exact_mod_cast h1

/-- On a smooth variety a prime divisor of multiplicity less than two at one of its points has
multiplicity exactly one there. -/
private theorem multiplicityAt_eq_one_of_toNat_lt_two {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of k)} (hsm : IsSmoothScheme sY)
    (D : Mori.PrimeDivisor Y) {y : Y} (hy : y ∈ D.support)
    (h2 : (D.multiplicityAt y).toNat < 2) : D.multiplicityAt y = 1 := by
  have h1 := one_le_toNat_multiplicityAt hsm D hy
  rw [← ENat.natCast_toNat (MMP.Threefold.Resolution.multiplicityAt_ne_top D
    (MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm D) y)]
  norm_cast
  omega

/-- If `Θ` is effective, the multiplicities at `x` of any finite set of prime divisors which all
have coefficient `1` in `Θ` sum to at most `mult_x Θ`. -/
private theorem natCast_sum_multiplicityAt_le {Y : Scheme.{u}} {Θ : QDivisor Y} {x : Y}
    (hnn : ∀ D, 0 ≤ Θ D) (S : Finset (Mori.PrimeDivisor Y)) (hS : ∀ D ∈ S, Θ D = 1) :
    ((∑ D ∈ S, (D.multiplicityAt x).toNat : ℕ) : ℚ) ≤ DivisorWithCoeffs.multiplicityAt Θ x := by
  classical
  have hmult : DivisorWithCoeffs.multiplicityAt Θ x =
      ∑ D ∈ S ∪ Θ.support, (D.multiplicityAt x).toNat • Θ D := by
    unfold DivisorWithCoeffs.multiplicityAt
    exact Finsupp.sum_of_support_subset _ Finset.subset_union_right _ (fun _ _ => smul_zero _)
  rw [hmult, Nat.cast_sum]
  refine le_of_eq_of_le (Finset.sum_congr rfl fun D hD => by rw [hS D hD, nsmul_one])
    (Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      fun D _ _ => nsmul_nonneg (hnn D) _)

/-- A boundary point `(C, y)` on `E_1` with `(C · E_1)_y ≥ 2`, where `C` and `E_1` have
coefficient `1` in the log pullback, makes `(X, B)` not log canonical near `P`: either `C` or
`E_1` is singular at `y`, or they are tangent there. -/
private theorem not_isLogCanonical_of_two_le_localIntersectionNumber_single
    {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] {P : X} {B : QDivisor X} {f : Y ⟶ X} [QuasiCompact (f ≫ sX)]
    [IsLocallyNoetherian Y] [IsNormal Y] {E : Fin 1 → Mori.PrimeDivisor Y}
    (ha : IsGermLogDiscrepancyVector sX P B f E 0)
    (hnn : ∀ D, 0 ≤ logPullbackBoundary f B E 0 D) {C : Mori.PrimeDivisor Y} {y : Y}
    (hCE : E 0 ≠ C) (hC : logPullbackBoundary f B E 0 C = 1)
    (hE : logPullbackBoundary f B E 0 (E 0) = 1) (hyC : y ∈ C.support)
    (hyE : y ∈ (E 0).support) (hycl : IsClosed ({y} : Set Y)) (hyP : f.base y = P)
    (hint : 2 ≤ localIntersectionNumber (f ≫ sX) y (Finsupp.single C 1) (Finsupp.single (E 0) 1))
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 2) :
    ¬ HoldsOnGerm {P} fun U : X.Opens => ∀ [Nonempty U],
      haveI : CompactSpace U := isCompact_iff_compactSpace.mp
        (@NoetherianSpace.isCompact _ _ (haveI : IsNoetherian X := {}; inferInstance) _)
      IsLogCanonical (U.ι ≫ sX) 2 (DivisorWithCoeffs.restrictOpen U K)
        (DivisorWithCoeffs.restrictOpen U (QDivisor.toRDivisor B)) := by
  classical
  have hg := ha.2.1
  have hYv := hg.isVariety
  have hsm := hg.isSmoothResolution.isSmoothScheme
  have h1C := one_le_toNat_multiplicityAt hsm _ hyC
  have h1E := one_le_toNat_multiplicityAt hsm _ hyE
  by_cases hsing : 3 ≤ (C.multiplicityAt y).toNat + ((E 0).multiplicityAt y).toNat
  · refine ha.not_isLogCanonical_of_two_lt_multiplicityAt hycl hyP (lt_of_lt_of_le ?_
      (natCast_sum_multiplicityAt_le hnn {C, E 0} (by simp [hC, hE]))) hK
    rw [Finset.sum_pair hCE.symm]
    exact_mod_cast hsing
  · exact ha.not_isLogCanonical_of_two_le_localIntersectionNumber hycl hyP (fun D _ => hnn D)
      hCE.symm hC hE
      ((MMP.Threefold.Resolution.multiplicityAt_eq_one_iff_exists_mem_smoothLocus hYv hsm
        hg.topologicalKrullDim_eq _ hyC).mp
        (multiplicityAt_eq_one_of_toNat_lt_two hsm _ hyC (by omega)))
      ((MMP.Threefold.Resolution.multiplicityAt_eq_one_iff_exists_mem_smoothLocus hYv hsm
        hg.topologicalKrullDim_eq _ hyE).mp
        (multiplicityAt_eq_one_of_toNat_lt_two hsm _ hyE (by omega)))
      hint hK

/-- **A single exceptional curve with `β_1 = 2`** (FA 3.3.2). Let `(X, P; B)` be a surface germ
with reduced boundary, `f : Y ⟶ X` its minimal resolution with one exceptional curve `E_1`, and
`Γ` the extended dual graph `Γ^*(f)` with boundary points `pt`. Suppose that `Γ(f)` is a
rational tree with `β_1 = 2`, and that `Γ^*(f)` does not consist of `v_1` and exactly two
boundary points `(C_1, y_1)`, `(C_2, y_2)` with `y_1 ≠ y_2`, each joined to `v_1` by an edge of
weight `1`. Then `(X, B)` is not log canonical near `P`: on no open neighbourhood `U` of `P` is
`(U, B|_U)` log canonical with canonical divisor `K_X|_U`. -/
@[mmp "lem_fa3_case9_single_vertex_distinct_points"]
public theorem IsExtendedDualGraph.not_isLogCanonical_of_boundary_eq_two
    {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] {P : X} {B : QDivisor X} {f : Y ⟶ X} [QuasiCompact (f ≫ sX)]
    [IsLocallyNoetherian Y] [IsNormal Y] {m : ℕ} {E : Fin 1 → Mori.PrimeDivisor Y}
    {pt : Fin m → Mori.PrimeDivisor Y × Y} {Γ : ExtendedWeightedGraph (Fin 1) (Fin m)}
    (hf : IsMinimalGermResolution sX P f) (h : IsExtendedDualGraph sX P B f E pt Γ)
    (hΓ : Γ.toWeightedGraph.IsRationalTree) (hβ : Γ.toWeightedGraph.boundary 0 = 2)
    (hpt : ¬ ∃ l₁ l₂ : Fin m, l₁ ≠ l₂ ∧ (∀ l, l = l₁ ∨ l = l₂) ∧ (pt l₁).2 ≠ (pt l₂).2 ∧
      Γ.boundaryEdgeWeight 0 l₁ = 1 ∧ Γ.boundaryEdgeWeight 0 l₂ = 1)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 2) :
    ¬ HoldsOnGerm {P} fun U : X.Opens => ∀ [Nonempty U],
      haveI : CompactSpace U := isCompact_iff_compactSpace.mp
        (@NoetherianSpace.isCompact _ _ (haveI : IsNoetherian X := {}; inferInstance) _)
      IsLogCanonical (U.ι ≫ sX) 2 (DivisorWithCoeffs.restrictOpen U K)
        (DivisorWithCoeffs.restrictOpen U (QDivisor.toRDivisor B)) := by
  classical
  have hW := h.isWeightedDualGraph
  have hg := hW.isGermResolution
  have hBs := hW.isSurfaceGermWithBoundary
  have hsm := hg.isSmoothResolution.isSmoothScheme
  have ha := isGermLogDiscrepancyVector_zero_of_boundary_eq_two hW hΓ hβ
  have hE0 := hW.isExceptionalCurveEnumeration.isGermExceptionalCurve 0
  have hcomp := fun C (hC : C ∈ (inverseTransformDivisor f B).support) =>
    logPullbackBoundary_zero_apply_of_mem_support hg hBs h.isReducedBoundary hE0 hC
  have hΘE := logPullbackBoundary_zero_apply_self hg hBs hE0
  have hΘnn := logPullbackBoundary_zero_nonneg hg hBs hE0
  have hallE := mem_support_of_isExtendedDualGraph h
  have hbp : ∀ l, (pt l).1 ∈ (inverseTransformDivisor f B).support ∧
      (pt l).2 ∈ (pt l).1.support ∧ f.base (pt l).2 = P ∧ IsClosed ({(pt l).2} : Set Y) := by
    intro l
    obtain ⟨hC, hy, hyP⟩ := h.isGermBoundaryPoint l
    have hC' : (pt l).1 ∈ (inverseTransformDivisor f B).support := Finsupp.mem_support_iff.mpr hC
    exact ⟨hC', hy, hyP,
      isClosed_singleton_of_mem_inter hg.topologicalKrullDim_eq (hcomp _ hC').2 ⟨hallE l, hy⟩⟩
  obtain ⟨hsum, hpos⟩ := h.boundary_eq_sum_boundaryEdgeWeight 0
  rw [hβ, Finset.filter_true_of_mem fun l _ => hallE l] at hsum
  by_cases hA : ∃ l, 2 ≤ Γ.boundaryEdgeWeight 0 l
  · obtain ⟨l, hl⟩ := hA
    obtain ⟨hC, hyC, hyP, hycl⟩ := hbp l
    rw [h.boundaryEdgeWeight_eq 0 l, if_pos (hallE l)] at hl
    exact not_isLogCanonical_of_two_le_localIntersectionNumber_single ha hΘnn (hcomp _ hC).2
      (hcomp _ hC).1 hΘE hyC (hallE l) hycl hyP hl hK
  push Not at hA
  have hw1 : ∀ l, Γ.boundaryEdgeWeight 0 l = 1 := fun l =>
    Nat.le_antisymm (Nat.le_of_lt_succ (hA l)) (hpos l (hallE l))
  simp only [hw1, Nat.cast_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hsum
  obtain rfl : m = 2 := by exact_mod_cast hsum.symm
  by_cases hy : (pt 0).2 = (pt 1).2
  · have hC01 : (pt 0).1 ≠ (pt 1).1 := fun hc => absurd (h.injective (Prod.ext hc hy)) (by decide)
    obtain ⟨hC0, hyC0, hyP, hycl⟩ := hbp 0
    obtain ⟨hC1, hyC1, -, -⟩ := hbp 1
    refine ha.not_isLogCanonical_of_two_lt_multiplicityAt hycl hyP (lt_of_lt_of_le ?_
      (natCast_sum_multiplicityAt_le hΘnn {(pt 0).1, (pt 1).1, E 0}
        (by simp [(hcomp _ hC0).1, (hcomp _ hC1).1, hΘE]))) hK
    rw [Finset.sum_insert (by simp [hC01, (hcomp _ hC0).2.symm]),
      Finset.sum_pair (hcomp _ hC1).2.symm]
    have := one_le_toNat_multiplicityAt hsm _ hyC0
    have := one_le_toNat_multiplicityAt hsm _ (show (pt 0).2 ∈ (pt 1).1.support by rwa [hy])
    have := one_le_toNat_multiplicityAt hsm _ (hallE 0)
    exact_mod_cast (show 2 < _ by omega)
  exact (hpt ⟨0, 1, by decide, fun l => by fin_cases l <;> simp, hy, hw1 0, hw1 1⟩).elim
