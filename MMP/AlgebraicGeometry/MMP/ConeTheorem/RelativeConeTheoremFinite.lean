module

public import MMP.AlgebraicGeometry.MMP.ConeTheorem.RelativeConeTheorem
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.BoundedCurveClasses
public import MMP.AlgebraicGeometry.Positivity.RelativeKodairaDecomposition

/-!
# The relative cone theorem: finitely many rays away from `K + Δ + εH`

Let `(X, Δ)` be a klt pair with `Δ` effective, and let `f : X ⟶ Y` be a morphism of projective
varieties over an algebraically closed field `k` of characteristic zero. For every `ε > 0` and
every `f`-ample Cartier divisor `H` on `X` there are finitely many rational curves `Cⱼ ⊆ X`, each
contracted by `f` and with `0 < -((K_X + Δ) · Cⱼ) ≤ 2 dim X`, such that

`NE̅(X/Y) = NE̅(X/Y)_{(K_X + Δ + εH) ≥ 0} + ∑ⱼ ℝ_{≥0} [Cⱼ]`.

By the relative cone theorem there are countably many rational curves `Cⱼ` contracted by `f`,
with `0 < -((K_X + Δ) · Cⱼ) ≤ 2 dim X`, such that
`NE̅(X/Y) = NE̅(X/Y)_{(K_X + Δ) ≥ 0} + ∑ⱼ ℝ_{≥0}[Cⱼ]`. Since `H` is `f`-ample it is positive on
the contracted curves, hence non-negative on `NE̅(X/Y)`. Every curve `Cⱼ` with
`((K_X + Δ + εH) · Cⱼ) ≥ 0` can therefore be absorbed into the part of `NE̅(X/Y)` where
`K_X + Δ + εH` is non-negative. The remaining curves satisfy `(H · Cⱼ) < 2 dim X / ε`. For an
ample `M` on `Y` and `ν ≫ 0` the divisor `H' = H + ν f^*M` is ample, and `(H' · Cⱼ) = (H · Cⱼ)`
because `(f^*M · Cⱼ) = (M · f_*Cⱼ) = 0`. Only finitely many classes of curves have bounded degree
against an ample divisor, and `N₁(X/Y) → N₁(X)` is injective, so the remaining curves have
finitely many classes.

## Main results

* `MMP.Mori.IsKltPair.exists_relativeClosedConeOfCurves_eq_add_hull_of_isRelativelyAmple`: the
  decomposition with finitely many rays.

## Implementation notes

The finite family of curves is indexed by a finite type `ι`; `∑ⱼ ℝ_{≥0}[Cⱼ]` is the convex cone
`PointedCone.hull ℝ` spanned by the classes `[Cⱼ]`. The pairing with the `ℝ`-divisor
`K_X + Δ + εH` on `N₁(X/Y)` is written as the sum of `MMP.Fourfold.QDivisor.relativeCurveForm`
of `K_X + Δ` and `ε` times the degree `MMP.Mori.RelativeNumericalCurveClasses.degree` of
`𝒪_X(H)`, so that `ε` ranges over all positive reals. The dimension of `X` is the integer `n`
of the klt pair.

## References

* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, Theorem 3.25(2) in
  case 3.21(0).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Pointwise MMP.Fourfold

namespace MMP.Mori

section Helpers

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- `deg_C 𝒪_X(E + E') = deg_C 𝒪_X(E) + deg_C 𝒪_X(E')` along a proper curve. -/
private theorem degree_cartierSheaf_add {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX) (E E' : X.CartierDivisor) :
    C.degree k (MMP.CartierDivisor.sheaf (E + E')) =
      C.degree k (MMP.CartierDivisor.sheaf E) +
        C.degree k (MMP.CartierDivisor.sheaf E') := by
  haveI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
        X.toRingedSpace.IsSheaf⟩).obj (MMP.CartierDivisor.sheaf E)).obj
          (MMP.CartierDivisor.sheaf E')) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf X.ringCatSheaf.2 _ _
  unfold ProperCurve.degree
  rw [← degreeOn_tensorSheaf]
  exact (degreeOn_eq_of_iso k sX C.ι C.dim_le
    (L := ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
        X.toRingedSpace.IsSheaf⟩).obj (MMP.CartierDivisor.sheaf E)).obj
          (MMP.CartierDivisor.sheaf E'))
    (MMP.CartierDivisorSheaf.sheafMulIso E E')).symm

/-- The pairing `E ↦ (z · E)` of a class `z ∈ N₁(X)` with Cartier divisors, additive in `E`. -/
private noncomputable def cartierPairing {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} (z : NumericalCurveClasses sX) : X.CartierDivisor →+ ℝ :=
  AddMonoidHom.mk' (fun E => NumericalCurveClasses.intersectionNumber
      (KCartierDivisor.ofCartier ℝ E) z) fun E E' => by
    obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
    simp only [NumericalCurveClasses.intersectionNumber_numericalClass,
      OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_apply]
    rw [← Finsupp.sum_add]
    refine Finsupp.sum_congr fun C _ => ?_
    rw [degree_cartierSheaf_add]
    push_cast
    ring

private theorem cartierPairing_apply {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} (z : NumericalCurveClasses sX) (E : X.CartierDivisor) :
    cartierPairing z E =
      NumericalCurveClasses.degree sX (MMP.CartierDivisor.sheaf E) z := by
  change NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ E) z = _
  rw [NumericalCurveClasses.intersectionNumber_ofCartier]

/-- Isomorphic invertible sheaves have the same degree form on `N₁(X)`. -/
private theorem degree_eq_of_iso {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {L L' : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L'] (e : L ≅ L') :
    NumericalCurveClasses.degree sX L = NumericalCurveClasses.degree sX L' := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun Z => ?_)
  change OneCycle.degree ℝ sX L Z = OneCycle.degree ℝ sX L' Z
  rw [OneCycle.degree, OneCycle.degree]
  congr 2
  funext C
  exact congrArg _ (degreeOn_eq_of_iso k sX C.ι C.dim_le e)

/-- The degree form on `N₁(X)` restricts along `N₁(X/Y) → N₁(X)` to the degree form on
`N₁(X/Y)`. -/
private theorem degree_relativeToAbsolute {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {f : X ⟶ Y} (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (z : RelativeNumericalCurveClasses sX f) :
    NumericalCurveClasses.degree sX L (relativeToAbsolute sX f z) =
      RelativeNumericalCurveClasses.degree sX f L z := by
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  rfl

/-- A projective variety carries a Cartier divisor whose sheaf is ample. -/
private theorem exists_isAmple_cartierSheaf {k : Type} [Field k] {Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} (hY : MMP.Mori.IsProjectiveVariety k sY) :
    ∃ M : Y.CartierDivisor,
      Stacks.Ample.IsAmple Y (MMP.CartierDivisor.sheaf M) := by
  haveI : IsIntegral Y := hY.toIsIntegral
  obtain ⟨H, hH, hHa⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hY
  obtain ⟨M, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf H
  exact ⟨M, (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mp
    ((Stacks.AmpleBridge.isAmple_iff_isAmple Y H).mpr hHa)⟩

/-- An `f`-ample invertible sheaf has non-negative degree on `NE̅(X/Y)`. -/
private theorem degree_nonneg_of_mem_relativeClosedConeOfCurves {k : Type} [Field k]
    {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsVariety k sX) (f : X ⟶ Y)
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (hL : IsRelativelyAmple f L)
    {z : RelativeNumericalCurveClasses sX f} (hz : z ∈ relativeClosedConeOfCurves sX f) :
    0 ≤ RelativeNumericalCurveClasses.degree sX f L z := by
  rw [← SetLike.mem_coe, coe_relativeClosedConeOfCurves] at hz
  refine closure_minimal (fun w hw => ?_) (isClosed_le continuous_const
    (RelativeNumericalCurveClasses.continuous_degree sX f L)) hz
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨C, hC⟩, rfl⟩ := hx
    change 0 ≤ OneCycle.degree ℝ sX L (C.cycle ℝ)
    rw [OneCycle.degree_cycle]
    exact_mod_cast (MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple hX f L hL C
      hC).le
  | zero => simp
  | add x y _ _ hx hy =>
    change 0 ≤ RelativeNumericalCurveClasses.degree sX f L (x + y)
    rw [map_add]
    exact add_nonneg hx hy
  | smul a x _ hx =>
    change 0 ≤ RelativeNumericalCurveClasses.degree sX f L ((a : ℝ) • x)
    rw [map_smul, smul_eq_mul]
    exact mul_nonneg a.2 hx

/-- **Absorbing rays into a half-space.** Let `N` be a convex cone, `ψ` and `d` linear forms with
`d ≥ 0` on `N`, and `ε ≥ 0`. If `N = N_{ψ ≥ 0} + hull (g j)` with every `g j ∈ N`, and every
generator `g j` with `(ψ + ε d)(g j) < 0` is among the `g' i ∈ N`, then
`N = N_{ψ + ε d ≥ 0} + hull (g' i)`. -/
private theorem coe_eq_add_hull_of_absorb {V : Type*} [AddCommGroup V] [Module ℝ V]
    (N : PointedCone ℝ V) (ψ d : V →ₗ[ℝ] ℝ) {ε : ℝ} (hε : 0 ≤ ε) (hd : ∀ z ∈ N, 0 ≤ d z)
    {ι₀ ι : Type*} (g : ι₀ → V) (g' : ι → V) (hg : ∀ j, g j ∈ N) (hg' : ∀ i, g' i ∈ N)
    (heq : (N : Set V) = {z | z ∈ N ∧ 0 ≤ ψ z} + (PointedCone.hull ℝ (Set.range g) : Set V))
    (hab : ∀ j, ψ (g j) + ε * d (g j) < 0 → g j ∈ Set.range g') :
    (N : Set V) = {z | z ∈ N ∧ 0 ≤ ψ z + ε * d z} +
      (PointedCone.hull ℝ (Set.range g') : Set V) := by
  let P : PointedCone ℝ V :=
    { carrier := {z | z ∈ N ∧ 0 ≤ ψ z + ε * d z}
      add_mem' := fun {a b} ha hb => ⟨N.add_mem ha.1 hb.1, by
        simp only [map_add]; nlinarith [ha.2, hb.2]⟩
      zero_mem' := ⟨N.zero_mem, by simp⟩
      smul_mem' := fun c z hz => ⟨Submodule.smul_mem N c hz.1, by
        change 0 ≤ ψ ((c : ℝ) • z) + ε * d ((c : ℝ) • z)
        simp only [map_smul, smul_eq_mul]
        nlinarith [hz.2, c.2]⟩ }
  have hhull' : PointedCone.hull ℝ (Set.range g') ≤ N :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr hg')
  apply Set.Subset.antisymm
  · intro z hz
    rw [heq] at hz
    obtain ⟨a, ⟨haN, ha⟩, h, hh, rfl⟩ := hz
    have hle : PointedCone.hull ℝ (Set.range g) ≤ P ⊔ PointedCone.hull ℝ (Set.range g') := by
      refine Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j => ?_)
      by_cases hj : ψ (g j) + ε * d (g j) < 0
      · exact (le_sup_right : PointedCone.hull ℝ (Set.range g') ≤ _)
          (Submodule.subset_span (hab j hj))
      · exact (le_sup_left : P ≤ _) ⟨hg j, le_of_not_gt hj⟩
    obtain ⟨p, hp, h', hh', rfl⟩ := Submodule.mem_sup.mp (hle hh)
    have haP : a ∈ P := ⟨haN, by nlinarith [hd a haN]⟩
    exact ⟨a + p, P.add_mem haP hp, h', hh', add_assoc _ _ _⟩
  · rintro _ ⟨a, ha, h, hh, rfl⟩
    exact N.add_mem ha.1 (hhull' hh)

/-- A contracted curve has its relative class in `NE̅(X/Y)`. -/
private theorem relativeClass_mem_relativeClosedConeOfCurves {k : Type} [Field k]
    {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {f : X ⟶ Y} {C : ProperCurve sX}
    (hC : C.IsContractedBy f) : C.relativeClass f hC ∈ relativeClosedConeOfCurves sX f := by
  rw [← SetLike.mem_coe, coe_relativeClosedConeOfCurves]
  exact subset_closure (relativeClass_mem_relativeConeOfCurves hC)

/-- **Boundedness of curve classes over `Y`.** For a morphism `f : X ⟶ Y` of projective varieties
over an algebraically closed field of characteristic zero and an `f`-ample invertible sheaf `L`,
only finitely many classes in `N₁(X/Y)` of curves contracted by `f` have `L`-degree at most `c`. -/
private theorem finite_relativeClass_degree_le {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} (sY : Y ⟶ Spec (.of k))
    [hXp : MMP.Mori.IsProjectiveVariety k sX] [hYp : MMP.Mori.IsProjectiveVariety k sY]
    {f : X ⟶ Y} (hf : f ≫ sY = sX) (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (hL : IsRelativelyAmple f L)
    (c : ℝ) :
    {z : RelativeNumericalCurveClasses sX f | ∃ (C : ProperCurve sX) (hC : C.IsContractedBy f),
      C.relativeClass f hC = z ∧ RelativeNumericalCurveClasses.degree sX f L z ≤ c}.Finite := by
  haveI : IsIntegral X := hXp.toIsIntegral
  haveI : IsIntegral Y := hYp.toIsIntegral
  obtain ⟨H₀, ⟨eH⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf L
  obtain ⟨M, hM⟩ := exists_isAmple_cartierSheaf hYp
  obtain ⟨B, ⟨eB⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf
    ((Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf M))
  obtain ⟨ν, hν⟩ := (MMP.Foundations.isAmple_add_zsmul_pullback k hXp hYp hf
    ((Stacks.RelativeVeryAmple.isAmple_congr _ _ (Iso.refl (MMP.CartierDivisor.sheaf M))).mpr hM)
    (Fourfold.isRelativelyAmple_of_iso f (eH) hL)
    ⟨eB.symm⟩).exists
  have hS := (MMP.Mori.isCompact_closedConeOfCurves_inter_le_and_finite sX _
    ((Stacks.RelativeVeryAmple.isAmple_congr _ _
      (Iso.refl (MMP.CartierDivisor.sheaf (H₀ + ν • B)))).mp hν)
    c).2
  have hinj : Function.Injective (relativeToAbsolute sX f) :=
    (MMP.Mori.existsUnique_isNaturalRelativeMap_and_injective sX f).2 _
      (isNaturalRelativeMap_relativeToAbsolute sX f)
  refine (hS.preimage hinj.injOn).subset ?_
  rintro _ ⟨C, hC, rfl, hc⟩
  refine ⟨C.cycle ℤ, fun D => ?_, ?_, ?_⟩
  · classical
    unfold ProperCurve.cycle
    rw [Finsupp.single_apply]
    split_ifs <;> norm_num
  · simp only [ProperCurve.cycle, Finsupp.mapRange_single, Int.cast_one]
    rfl
  · change cartierPairing (relativeToAbsolute sX f (C.relativeClass f hC)) (H₀ + ν • B) ≤ c
    have hB0 : cartierPairing (relativeToAbsolute sX f (C.relativeClass f hC)) B = 0 := by
      rw [cartierPairing_apply, degree_eq_of_iso eB.symm,
        ← NumericalCurveClasses.degree_pushforward f hf,
        LinearMap.mem_ker.mp (range_relativeToAbsolute_le_ker_pushforward f hf ⟨_, rfl⟩),
        map_zero]
    rw [map_add, map_zsmul, hB0, smul_zero, add_zero, cartierPairing_apply, ← degree_eq_of_iso eH,
      degree_relativeToAbsolute]
    exact hc

end Helpers

/-- **The relative cone theorem, finiteness part.** Let `(X, Δ)` be a klt pair (canonical divisor
`K`, `n = dim X`) with `Δ` effective, over an algebraically closed field of characteristic zero,
`f : X ⟶ Y` a morphism of projective varieties, `ε > 0` and `H` an `f`-ample Cartier divisor on
`X`. Then there is a finite family of rational curves `C j` contracted by `f`, with
`0 < -((K + Δ) · [C j]) ≤ 2n`, such that `relativeClosedConeOfCurves sX f` is the sum of its part
where `K + Δ + εH` is non-negative and the convex cone spanned by the classes `[C j]`. -/
@[mmp "thm_km3b_relative_cone_theorem_finite"]
public theorem IsKltPair.exists_relativeClosedConeOfCurves_eq_add_hull_of_isRelativelyAmple
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} (sY : Y ⟶ Spec (.of k)) [IsProjectiveVariety k sX]
    [IsProjectiveVariety k sY] [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] (f : X ⟶ Y) (hf : f ≫ sY = sX)
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (hΔ : IsKltPair sX n K Δ) (hΔ0 : 0 ≤ Δ)
    {ε : ℝ} (hε : 0 < ε) {H : Divisor X} (hH : H.IsCartier) (hHf : H.IsRelativelyAmple f hH) :
    haveI := hH.isInvertibleModule_divisorialSheaf
    ∃ (ι : Type) (_ : Finite ι) (C : ι → ProperCurve sX)
      (hC : ∀ j, (C j).IsContractedBy f),
      (∀ j, IsRationalCurve sX
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({(C j).point} : Set X)))) ∧
      (∀ j, 0 < -QDivisor.relativeCurveForm sX f (Divisor.toQDivisor K + Δ) hΔ.1.2.2
          ((C j).relativeClass f (hC j)) ∧
        -QDivisor.relativeCurveForm sX f (Divisor.toQDivisor K + Δ) hΔ.1.2.2
          ((C j).relativeClass f (hC j)) ≤ 2 * n) ∧
      (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f)) =
        {z | z ∈ relativeClosedConeOfCurves sX f ∧
          0 ≤ QDivisor.relativeCurveForm sX f (Divisor.toQDivisor K + Δ) hΔ.1.2.2 z +
            ε * RelativeNumericalCurveClasses.degree sX f H.divisorialSheaf z} +
        (PointedCone.hull ℝ (Set.range fun j => (C j).relativeClass f (hC j)) :
          Set (RelativeNumericalCurveClasses sX f)) := by
  haveI := hH.isInvertibleModule_divisorialSheaf
  obtain ⟨ι₀, -, C, hC, hrat, hbd, heq⟩ :=
    hΔ.exists_relativeClosedConeOfCurves_eq_add_hull sY f hf hΔ0
  set ψ := QDivisor.relativeCurveForm sX f (Divisor.toQDivisor K + Δ) hΔ.1.2.2
  set dH := RelativeNumericalCurveClasses.degree sX f H.divisorialSheaf
  set g : ι₀ → RelativeNumericalCurveClasses sX f := fun j => (C j).relativeClass f (hC j)
  -- the rays on which `K + Δ + εH` is negative have `(H · Cⱼ) < 2n / ε`
  let J := {j : ι₀ // ψ (g j) + ε * dH (g j) < 0}
  have hfin : (Set.range fun j : J => g j.1).Finite := by
    refine (finite_relativeClass_degree_le sY hf _ hHf (2 * n / ε)).subset ?_
    rintro _ ⟨j, rfl⟩
    refine ⟨C j.1, hC j.1, rfl, ?_⟩
    rw [le_div_iff₀ hε]
    linarith [j.2, (hbd j.1).2]
  let ι := ↥(Set.range fun j : J => g j.1)
  let pick : ι → J := fun x => Classical.choose x.2
  refine ⟨ι, hfin.to_subtype, fun x => C (pick x).1, fun x => hC _, fun x => hrat _,
    fun x => hbd _, coe_eq_add_hull_of_absorb _ ψ dH hε.le
      (fun z hz => degree_nonneg_of_mem_relativeClosedConeOfCurves inferInstance f _ hHf hz)
      g _ (fun j => relativeClass_mem_relativeClosedConeOfCurves _)
      (fun x => relativeClass_mem_relativeClosedConeOfCurves _) heq
      fun j hj => ⟨⟨_, ⟨j, hj⟩, rfl⟩, Classical.choose_spec (⟨_, ⟨j, hj⟩, rfl⟩ : ι).2⟩⟩

end MMP.Mori
