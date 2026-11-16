module

public import MMP.AlgebraicGeometry.Positivity.NefThresholdConvexity
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
public import MMP.AlgebraicGeometry.Positivity.AmplePlusNefSum

@[expose] public section

section

/-!
# The test divisors of the rationality theorem are ample

Let `(X, Δ, a, H)` be a rationality datum with nef threshold `r`, `p, q > 0` integers with
`aq - rp > 0`, `(f; F_•; a_•; p_•; r_•)` a `(p, q)`-adapted resolution with tie-breaker `(j₀, c)`,
and `p', q'` integers with `p' ≥ (1 + c) p`, `q' ≥ (1 + c) q` and `aq' - rp' ≤ aq - rp`. Then the
test divisor `N(p', q') = f^*(p'H + q'a(K_X + Δ)) + A' - F_{j₀} - K_Y` is ample.

Write `K = K_X + Δ`, `M = pH + qaK`, `R = ∑_j r_j F_j` and `L = f^*M - R`. Since
`-c r_{j₀} + a_{j₀} - p_{j₀} = -1` and `K_Y - ∑_j a_j F_j ∼ f^*K` (KM 2.26), up to numerical
equivalence
`N(p', q') ≡ (f^*(pH + (qa - 1)K) - ∑_j p_j F_j) + (c L + f^*(xH + tK))`
with `x = p' - (1 + c) p` and `t = (q' - (1 + c) q) a`. The first summand is ample; `L` is nef
because the effective divisor `f^*(σ)₀ - R`, linearly equivalent to it, misses any given point;
and `0 ≤ t < rx` makes `xH + tK` nef, hence also its pull-back. Ample plus nef is ample.

## Main results

* `MMP.Mori.IsStripTieBreaker.isAmple_of_isStripTestDivisor`: `N(p', q')` is ample.

## Implementation notes

The test divisor is the relation `MMP.Mori.IsStripTestDivisor`: `N` is a test divisor for some
canonical divisor `K_Y` of `Y` and some pull-back of `p'H + q'a(K_X + Δ)`. The statement holds
for every such `N`. The inequalities `p' ≥ (1 + c) p` and `q' ≥ (1 + c) q` are read in `ℚ`, and
`aq' - rp' ≤ aq - rp` in `ℝ`, since `c` is rational and `r` real.

The base field `k` is arbitrary. As `f` is a log resolution, `X` is smooth at the generic points
of its prime divisors and at its generic point, so `K_X = div(ω)` for a rational top form `ω`,
and `K_Y - ∑_j a_j F_j ∼ f^*(K_X + Δ)` is proved coefficientwise from the definition of the
discrepancy and algebraic Hartogs.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Theorem 3.5, 3.4 Step 8
-/

namespace MMP.FourfoldProofs.Km3bStripTestDivisorAmpleProof

open CategoryTheory AlgebraicGeometry MMP.Mori

/-! ### Nefness -/

/-- A dominant morphism of integral schemes maps the generic point outside every divisor. -/
private theorem map_componentGenericPoint_notMem_supp {X : Scheme.{0}} [IsIntegral X]
    {Y : Scheme.{0}} [IsIntegral Y] (f : Y ⟶ X) [IsDominant f] {R : Type*} [Zero R]
    (D : DivisorWithCoeffs R X) (Z : irreducibleComponents Y) :
    f (componentGenericPoint Y Z) ∉ D.supp := by
  rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant]
  exact MMP.Fourfold.genericPoint_notMem_supp _

section Nef

variable {k : Type} [Field k]

/-- If `u ≫ s_W = s_V` and the curve `C ⊆ V` is not contracted by `u`, its image `u(C)` is a
proper curve in `W`. -/
private theorem isCurve_imageι_of_comp_eq {V W C : Scheme.{0}} {sV : V ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)} [AlgebraicGeometry.IsVariety k sW] {u : V ⟶ W} (hu : u ≫ sW = sV)
    (i : C ⟶ V) [AlgebraicGeometry.IsCurve k (i ≫ sV)] [IsProper (i ≫ sV)]
    (hpt : ¬ ∃ w : W, Set.range (i ≫ u) = {w}) :
    IsProper ((i ≫ u).imageι ≫ sW) ∧ AlgebraicGeometry.IsCurve k ((i ≫ u).imageι ≫ sW) := by
  have e : (i ≫ u) ≫ sW = i ≫ sV := by rw [Category.assoc, hu]
  have : IsProper ((i ≫ u) ≫ sW) := e ▸ inferInstance
  have : AlgebraicGeometry.IsCurve k ((i ≫ u) ≫ sW) := e ▸ inferInstance
  have : IsProper (i ≫ u) := IsProper.of_comp (i ≫ u) sW
  exact ⟨isProper_imageι_comp (i ≫ u) sW, isCurve_imageι_comp sW (i ≫ u) hpt⟩

/-- **The pull-back of a nef `ℚ`-divisor is nef.** For a morphism `u : V ⟶ W` of normal varieties
over `k` and a curve `C ⊆ V`, `(u^*L · C)` is `0` if `u(C)` is a point and a nonnegative multiple
of `(L · u(C))` otherwise. -/
private theorem isNef_of_isPullback {V W : Scheme.{0}} {sV : V ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)} [AlgebraicGeometry.IsVariety k sV]
    [AlgebraicGeometry.IsVariety k sW] [IsLocallyNoetherian V] [IsNormal V]
    [IsLocallyNoetherian W] [IsNormal W] {u : V ⟶ W} (hu : u ≫ sW = sV) {L : QDivisor W}
    (hL : L.IsNef k sW)
    {hLB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp}
    {L' : QDivisor V} (h : L.IsPullback u hLB L') : L'.IsNef k sV := by
  refine ⟨h.isQCartier hL.1, fun C i _ _ _ hC => ?_⟩
  have : AlgebraicGeometry.IsCurve k (i ≫ sV) := { topologicalKrullDim_eq_one := hC }
  by_cases hpt : ∃ w : W, Set.range (i ≫ u) = {w}
  · exact (intersectionNumber_pullback_eq_zero k sV sW u hu i hL.1 h hpt).ge
  · obtain ⟨_, hcurve⟩ := isCurve_imageι_of_comp_eq hu i hpt
    rw [intersectionNumber_pullback_eq_degreeOver_mul k sV sW u hu i hL.1 h hcurve]
    exact mul_nonneg (by positivity)
      (hL.2 _ (i ≫ u).imageι hcurve.topologicalKrullDim_eq_one)

/-- On a scheme all of whose `ℚ`-divisors are `ℚ`-Cartier (a smooth variety), the intersection
number with a fixed curve `C` is a `ℚ`-linear form `L ↦ (L · C)` on `ℚ`-divisors. -/
private noncomputable def intersectionLinearMap {W C : Scheme.{0}} [IsLocallyNoetherian W]
    [IsNormal W]
    (sW : W ⟶ Spec (.of k)) [QuasiCompact sW] (j : C ⟶ W) [IsProper (j ≫ sW)]
    (hdim : topologicalKrullDim C ≤ 1) (hQ : ∀ L : QDivisor W, L.IsQCartier) :
    QDivisor W →ₗ[ℚ] ℚ where
  toFun L := L.intersectionNumber k sW j hdim (hQ L)
  map_add' L L' := QDivisor.intersectionNumber_add' k sW j hdim L L' (hQ L) (hQ L') (hQ _)
  map_smul' q L := MMP.Fourfold.intersectionNumber_smul sW j hdim L (hQ L) q (hQ _)

private theorem intersectionLinearMap_apply {W C : Scheme.{0}} [IsLocallyNoetherian W]
    [IsNormal W] (sW : W ⟶ Spec (.of k)) [QuasiCompact sW] (j : C ⟶ W) [IsProper (j ≫ sW)]
    (hdim : topologicalKrullDim C ≤ 1) (hQ : ∀ L : QDivisor W, L.IsQCartier) (L : QDivisor W)
    (hL : L.IsQCartier) :
    intersectionLinearMap sW j hdim hQ L = L.intersectionNumber k sW j hdim hL := rfl

/-- **Linearity of the intersection number.** `((x L₂ + y L₃) · C) = x (L₂ · C) + y (L₃ · C)`. -/
private theorem intersectionNumber_smul_add_smul {W C : Scheme.{0}} [IsLocallyNoetherian W]
    [IsNormal W] (sW : W ⟶ Spec (.of k)) [QuasiCompact sW] (j : C ⟶ W) [IsProper (j ≫ sW)]
    (hdim : topologicalKrullDim C ≤ 1) {L₂ L₃ : QDivisor W} (h₂ : L₂.IsQCartier)
    (h₃ : L₃.IsQCartier) (x y : ℚ) (h₁ : (x • L₂ + y • L₃).IsQCartier) :
    (x • L₂ + y • L₃).intersectionNumber k sW j hdim h₁ =
      x * L₂.intersectionNumber k sW j hdim h₂ + y * L₃.intersectionNumber k sW j hdim h₃ := by
  have hx := MMP.Flips.QDivisor.IsQCartier.qsmul h₂ x
  have hy := MMP.Flips.QDivisor.IsQCartier.qsmul h₃ y
  rw [QDivisor.intersectionNumber_add' k sW j hdim _ _ hx hy,
    MMP.Fourfold.intersectionNumber_smul sW j hdim L₂ h₂ x hx,
    MMP.Fourfold.intersectionNumber_smul sW j hdim L₃ h₃ y hy]

/-- **The projection formula is linear in the divisor.** If `L₁ = x L₂ + y L₃` on `W` and `L_i'`
are the pull-backs along `u : V ⟶ W`, then `(L₁' · C) = x (L₂' · C) + y (L₃' · C)` for every
curve `C ⊆ V`: all three vanish if `u(C)` is a point, and otherwise are `deg(C → u(C))` times the
intersection numbers with `u(C)`. -/
private theorem intersectionNumber_isPullback_smul_add_smul {V W C : Scheme.{0}}
    {sV : V ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)} [AlgebraicGeometry.IsVariety k sV]
    [AlgebraicGeometry.IsVariety k sW] [IsLocallyNoetherian V] [IsNormal V]
    [IsLocallyNoetherian W] [IsNormal W] {u : V ⟶ W} (hu : u ≫ sW = sV) (i : C ⟶ V)
    [AlgebraicGeometry.IsCurve k (i ≫ sV)] [IsProper (i ≫ sV)] {L₂ L₃ : QDivisor W}
    (h₂ : L₂.IsQCartier) (h₃ : L₃.IsQCartier) (x y : ℚ) {L₁ : QDivisor W}
    (hL : L₁ = x • L₂ + y • L₃)
    {hB₁ : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L₁.supp}
    {hB₂ : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L₂.supp}
    {hB₃ : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L₃.supp}
    {L₁' L₂' L₃' : QDivisor V} (p₁ : L₁.IsPullback u hB₁ L₁')
    (p₂ : L₂.IsPullback u hB₂ L₂') (p₃ : L₃.IsPullback u hB₃ L₃') (h₁' : L₁'.IsQCartier)
    (h₂' : L₂'.IsQCartier) (h₃' : L₃'.IsQCartier) :
    L₁'.intersectionNumber k sV i (IsCurve.topologicalKrullDim_eq_one (f := i ≫ sV)).le h₁' =
      x * L₂'.intersectionNumber k sV i (IsCurve.topologicalKrullDim_eq_one (f := i ≫ sV)).le
          h₂' +
        y * L₃'.intersectionNumber k sV i (IsCurve.topologicalKrullDim_eq_one (f := i ≫ sV)).le
          h₃' := by
  have h₁ : L₁.IsQCartier := hL ▸ (MMP.Flips.QDivisor.IsQCartier.qsmul h₂ x).add
    (MMP.Flips.QDivisor.IsQCartier.qsmul h₃ y)
  subst hL
  by_cases hpt : ∃ w : W, Set.range (i ≫ u) = {w}
  · rw [intersectionNumber_pullback_eq_zero k sV sW u hu i h₁ p₁ hpt,
      intersectionNumber_pullback_eq_zero k sV sW u hu i h₂ p₂ hpt,
      intersectionNumber_pullback_eq_zero k sV sW u hu i h₃ p₃ hpt]
    ring
  · obtain ⟨_, hcurve⟩ := isCurve_imageι_of_comp_eq hu i hpt
    rw [intersectionNumber_pullback_eq_degreeOver_mul k sV sW u hu i h₁ p₁ hcurve,
      intersectionNumber_pullback_eq_degreeOver_mul k sV sW u hu i h₂ p₂ hcurve,
      intersectionNumber_pullback_eq_degreeOver_mul k sV sW u hu i h₃ p₃ hcurve,
      intersectionNumber_smul_add_smul sW _ _ h₂ h₃ x y h₁]
    ring

/-- If `H + tK` is nef in the sense of `QDivisor.IsNefCombination` for a rational `t`, then the
`ℚ`-divisor `H + tK` is nef. -/
private theorem isNef_add_smul_of_isNefCombination {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {H K : QDivisor X} {t : ℚ}
    (h : QDivisor.IsNefCombination k sX H K t) : (H + t • K).IsNef k sX := by
  obtain ⟨hH, hK, hC⟩ := h
  have htK : (t • K).IsQCartier := MMP.Flips.QDivisor.IsQCartier.qsmul hK t
  have hq : (H + t • K).IsQCartier := hH.add htK
  refine ⟨hq, fun C i _ _ _ hC' => ?_⟩
  rw [QDivisor.intersectionNumber_add' k sX i hC'.le H (t • K) hH htK hq,
    MMP.Fourfold.intersectionNumber_smul sX i hC'.le K hK t htK]
  exact_mod_cast hC C i hC'

/-- **A basepoint-free part is nef** (KM 3.2, Step 3). Let `f : Y ⟶ X` be a dominant morphism
of Noetherian normal integral schemes, every divisor on `Y` Cartier, `M` a Cartier divisor on `X`
with pull-back `M'`, and `R₀` a divisor on `Y` with `f^*(σ)₀ ≥ R₀` for every nonzero section `σ`
of `𝒪_X(M)`, every point of `Y` lying outside `Supp(f^*(σ)₀ - R₀)` for some `σ`. Then
`M' - R₀` is nef: on a curve `C ∋ y`, the effective divisor `f^*(σ)₀ - R₀ ∼ M' - R₀` does not
contain `C`. -/
private theorem isNef_sub_of_forall_exists_notMem_supp {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] {sY : Y ⟶ Spec (.of k)} [QuasiCompact sY] {f : Y ⟶ X}
    [IsDominant f] (hcart : ∀ D : Divisor Y, D.IsCartier) {M : Divisor X} (hM : M.IsCartier)
    {hMB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ M.supp}
    {M' : Divisor Y} (hM' : M.IsPullback f hMB M') (R₀ : Divisor Y)
    (hle : ∀ (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0),
      ∃ (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉
          (M.zeroDivisor σ hσ).supp) (Z' : Divisor Y),
        (M.zeroDivisor σ hσ).IsPullback f hB Z' ∧ R₀ ≤ Z')
    (hex : ∀ y : Y, ∃ (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0)
      (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉
          (M.zeroDivisor σ hσ).supp) (Z' : Divisor Y),
        (M.zeroDivisor σ hσ).IsPullback f hB Z' ∧ y ∉ ((Z' - R₀).supp : Set Y)) :
    (Divisor.toQDivisor (M' - R₀)).IsNef k sY := by
  rw [QDivisor.isNef_toQDivisor_iff _ (hcart _)]
  refine ⟨hcart _, fun C i _ _ _ hC => ?_⟩
  obtain ⟨c⟩ : Nonempty C := inferInstance
  obtain ⟨σ, hσ, hB, Z', hZ', hy⟩ := hex (i c)
  obtain ⟨hB', Z'', hZ'', hR⟩ := hle σ hσ
  have hZc : (M.zeroDivisor σ hσ).IsCartier := by
    rw [Divisor.zeroDivisor_eq]
    exact (Divisor.isCartier_principalDivisor _).add hM
  obtain rfl : Z' = Z'' := hZ'.eq hZc hZ''
  set φ := (Divisor.isUnit_sectionToRationalFunctions hσ).unit
  have hφB : ∀ Z : irreducibleComponents Y,
      f (componentGenericPoint Y Z) ∉ (principalDivisor φ).supp :=
    map_componentGenericPoint_notMem_supp f _
  have hP := Divisor.isPullback_principalDivisor (f := f) φ hφB
  have hsum := hP.add (Divisor.isCartier_principalDivisor φ) hM hB hM'
  have hZ2 : Z' = principalDivisor (pullbackRationalFunction f φ hφB) + M' :=
    hZ'.eq hZc (hsum.of_eq (Divisor.zeroDivisor_eq M σ hσ).symm)
  have heff : 0 ≤ Z' - R₀ := sub_nonneg.mpr hR
  have h0 := (MMP.Threefold.Mori.degreeOn_nonneg_and_eq_zero_iff sY i hC.le (Z' - R₀)
    (hcart _) heff ⟨c, hy⟩).1
  have hsplit : Z' - R₀ = principalDivisor (pullbackRationalFunction f φ hφB) + (M' - R₀) := by
    rw [hZ2]
    abel
  rwa [Divisor.degreeOn_congr hsplit (hcart _) ((hcart _).add (hcart _)),
    Divisor.degreeOn_add k sY i hC.le _ _ (hcart _) (hcart _),
    MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent sY i hC.le (hcart _)
      (Divisor.linearlyEquivalent_principalDivisor_zero _), zero_add] at h0

end Nef

/-! ### Orders of forms along prime divisors with smooth generic point -/

section Forms

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}

/-- For a formally smooth field extension `K / k`, essentially of finite type, the rank of
`Ω_{K/k}` is the transcendence degree of `K / k`. -/
private theorem finrank_kaehlerDifferential_eq_toNat_trdeg {K : Type*} [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] [Algebra.FormallySmooth k K] :
    Module.finrank K Ω[K⁄k] = (Algebra.trdeg k K).toNat := by
  have h := (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k K).2.2
  rw [Module.finrank_zero_of_subsingleton (M := Algebra.H1Cotangent k K), Nat.cast_zero,
    sub_zero] at h
  exact_mod_cast h.symm

/-- The local ring along a prime divisor of a scheme locally of finite type over `k` is
essentially of finite type over `k`. -/
private theorem essFiniteType_localRing [IsLocallyNoetherian X] [LocallyOfFiniteType sX]
    (Γ : MMP.Mori.PrimeDivisor X) :
    letI := stalkAlgebra sX Γ.genericPoint
    Algebra.EssFiniteType k Γ.localRing := by
  let := stalkAlgebra sX Γ.genericPoint
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ Γ.genericPoint) isOpen_univ
  have hU' : IsAffineOpen U := hU
  let x : U := ⟨Γ.genericPoint, hxU⟩
  let := sectionAlgebra sX U
  have := finiteType_sectionAlgebra sX hU'
  let : Algebra Γ(X, U) Γ.localRing := TopCat.Presheaf.algebra_section_stalk X.presheaf x
  have := isScalarTower_section_stalk sX U x
  have := hU'.isLocalization_stalk x
  set q := (hU'.primeIdealOf x).asIdeal
  have : Algebra.EssFiniteType Γ(X, U) Γ.localRing := .of_isLocalization _ q.primeCompl
  exact .comp k Γ(X, U) Γ.localRing

/-- **Generators of the top forms at a smooth prime divisor.** If the generic point of a prime
divisor `Γ` of a normal integral scheme `X` locally of finite type over `k` is a smooth point,
and `d = trdeg_k k(X)`, then `Ω^d_{𝒪_{X,Γ}/k}` has a generator with nonzero image in
`Ω^d_{k(X)/k}`. -/
private theorem exists_topForms_generator_of_mem_smoothLocus [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [LocallyOfFiniteType sX] (Γ : MMP.Mori.PrimeDivisor X)
    (hΓ : Γ.genericPoint ∈ smoothLocus sX) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d) :
    letI := stalkAlgebra sX Γ.genericPoint
    letI := functionFieldAlgebra sX
    haveI := isScalarTower_stalk_functionField sX Γ.genericPoint
    ∃ σ : ⋀[Γ.localRing]^d Ω[Γ.localRing⁄k], Submodule.span Γ.localRing {σ} = ⊤ ∧
      topFormsMap k Γ.localRing X.functionField d σ ≠ 0 := by
  let := stalkAlgebra sX Γ.genericPoint
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX Γ.genericPoint
  have := (MMP.Positivity.PrimeDivisor.genericPoint_mem_smoothLocus_iff Γ).mp hΓ
  have := essFiniteType_localRing (sX := sX) Γ
  have := Γ.isDiscreteValuationRing_localRing
  have : Module.Free Γ.localRing Ω[Γ.localRing⁄k] := Module.free_of_flat_of_isLocalRing
  have : Algebra.FormallySmooth Γ.localRing X.functionField :=
    .of_isLocalization (nonZeroDivisors Γ.localRing)
  have : Algebra.FormallySmooth k X.functionField := .comp k Γ.localRing X.functionField
  have := essFiniteType_functionField (sX := sX)
  exact exists_topForms_generator_of_free
    ((finrank_kaehlerDifferential_eq_of_isFractionRing (K := X.functionField)).symm.trans
      (finrank_kaehlerDifferential_eq_toNat_trdeg.trans hd))

/-- **The order of a form along a basis at a smooth prime divisor**: for a basis `b` of
`Ω^d_{k(X)/k}` there is an integer `N` with `ord_Γ(τ) = v_Γ(τ / b^{⊗m}) + m · N` for every `m`
and every nonzero rational `m`-canonical form `τ`. -/
private theorem exists_ordForm_eq_ord_add_mul_of_mem_smoothLocus [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [LocallyOfFiniteType sX] (Γ : MMP.Mori.PrimeDivisor X)
    (hΓ : Γ.genericPoint ∈ smoothLocus sX) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    (b : letI := functionFieldAlgebra sX
      Module.Basis Unit X.functionField (⋀[X.functionField]^d Ω[X.functionField⁄k])) :
    letI := functionFieldAlgebra sX
    ∃ N : ℤ, ∀ (m : ℤ) (τ : RationalPluriForms sX d m), τ ≠ 0 →
      Γ.ordForm τ = X.ord ((ZTensorPower.basis b m).repr τ ()) Γ.genericPoint + m * N := by
  let := stalkAlgebra sX Γ.genericPoint
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX Γ.genericPoint
  exact exists_ordAt_eq_add_mul (k := k) Γ.ord_mul_of_ne_zero
    (fun _ ha => Γ.ord_algebraMap_of_isUnit ha)
    (exists_topForms_generator_of_mem_smoothLocus Γ hΓ hd)
    b

/-- **Smoothness is transported by an isomorphism of local rings.** If `f : Y ⟶ X` is a
`k`-morphism inducing an isomorphism `𝒪_{X,f(y)} ≅ 𝒪_{Y,y}` and `Y` is smooth over `k` at `y`,
then `X` is smooth over `k` at `f(y)`. -/
private theorem map_mem_smoothLocus_of_isIso_stalkMap [LocallyOfFiniteType sX] {Y : Scheme.{0}}
    (f : Y ⟶ X) [LocallyOfFiniteType (f ≫ sX)] {y : Y} (hy : y ∈ smoothLocus (f ≫ sX))
    [IsIso (f.stalkMap y)] : f y ∈ smoothLocus sX := by
  have : LocallyOfFinitePresentation sX :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have : LocallyOfFinitePresentation (f ≫ sX) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  rw [smoothLocus_eq_smoothLocus, Scheme.Hom.mem_smoothLocus] at hy ⊢
  rw [Scheme.Hom.stalkMap_comp] at hy
  exact (RingHom.FormallySmooth.respectsIso.cancel_right_isIso _ _).mp hy

/-- **A smooth resolution is an isomorphism in codimension one, so the base is smooth in
codimension one.** If `f : Y ⟶ X` is a proper birational morphism of normal varieties with `Y`
smooth, the generic point of every prime divisor of `X` is a smooth point: it is the image of the
generic point of its strict transform, with isomorphic local rings. -/
private theorem genericPoint_mem_smoothLocus_of_isSmoothScheme [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (hX : IsNormalVariety k sX) {Y : Scheme.{0}}
    [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} [IsProper f]
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    (hsm : IsSmoothScheme (f ≫ sX)) (Γ : MMP.Mori.PrimeDivisor X) :
    Γ.genericPoint ∈ smoothLocus sX := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  obtain ⟨E, hE, hiso, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX hY hf Γ
  have hmem : E.genericPoint ∈ smoothLocus (f ≫ sX) := by
    rw [show smoothLocus (f ≫ sX) = ⊤ from hsm]
    trivial
  rw [← hE]
  exact map_mem_smoothLocus_of_isIso_stalkMap f hmem

/-- **Smoothness at a point.** For `X` locally of finite type over `k`, a point `x` is a smooth
point exactly when `𝒪_{X,x}` is formally smooth over `k`. -/
private theorem mem_smoothLocus_iff_formallySmooth [LocallyOfFiniteType sX] (x : X) :
    x ∈ smoothLocus sX ↔
      letI := stalkAlgebra sX x
      Algebra.FormallySmooth k (X.presheaf.stalk x) := by
  have : LocallyOfFinitePresentation sX :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  rw [smoothLocus_eq_smoothLocus, Scheme.Hom.mem_smoothLocus]
  let g : CommRingCat.of k ⟶ (Spec (.of k)).presheaf.stalk (sX x) :=
    (Scheme.ΓSpecIso (.of k)).inv ≫
      (Spec (.of k)).presheaf.germ ⊤ _ (TopologicalSpace.Opens.mem_top _)
  have hiso : IsIso g := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨RingHom.injective _, MMP.Positivity.surjective_algebraMap_stalk_Spec _⟩
  have hcomp : g ≫ sX.stalkMap x =
      (Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
        X.presheaf.germ ⊤ x (TopologicalSpace.Opens.mem_top _) := by
    erw [Category.assoc, Scheme.Hom.germ_stalkMap sX ⊤ x (TopologicalSpace.Opens.mem_top _)]
    rfl
  rw [← RingHom.FormallySmooth.respectsIso.cancel_left_isIso g, ← CommRingCat.hom_comp, hcomp]
  rfl

/-- **Pull-back generators along a birational morphism, at a smooth generic point.** If `X` is
integral, locally of finite type over `k` with smooth generic point, `trdeg_k k(X) = d`, and
`f^* : k(X) → k(Y)` is bijective, then `Ω^d_{k(X)/k}` has a generator whose pull-back generates
`Ω^d_{k(Y)/k}`. -/
private theorem exists_isPullbackGenerator_of_genericPoint_mem_smoothLocus [IsIntegral X]
    [LocallyOfFiniteType sX] (hη : genericPoint X ∈ smoothLocus sX) {Y : Scheme.{0}}
    [IsIntegral Y] (f : Y ⟶ X) [IsDominant f] (hf : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d) :
    letI := functionFieldAlgebra sX
    letI := functionFieldAlgebra (f ≫ sX)
    letI := functionFieldMapAlgebra f
    haveI := isScalarTower_functionFieldMap sX f
    ∃ ω : ⋀[X.functionField]^d Ω[X.functionField⁄k], IsPullbackGenerator Y.functionField ω := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  have : Algebra.FormallyEtale X.functionField Y.functionField :=
    Algebra.FormallyEtale.of_equiv
      (AlgEquiv.ofBijective (Algebra.ofId X.functionField Y.functionField) hf)
  have := essFiniteType_functionField (sX := sX)
  have : Algebra.FormallySmooth k X.functionField := (mem_smoothLocus_iff_formallySmooth _).mp hη
  exact exists_isPullbackGenerator_of_formallyEtale
    (finrank_kaehlerDifferential_eq_toNat_trdeg.trans hd)

/-- The pull-back of a nonzero rational form along a birational morphism, at a smooth generic
point, is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero [IsIntegral X] [LocallyOfFiniteType sX]
    (hη : genericPoint X ∈ smoothLocus sX) {n : ℕ} (hn : topologicalKrullDim X = n)
    {Y : Scheme.{0}} [IsIntegral Y] (f : Y ⟶ X) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) {m : ℤ} {τ : RationalPluriForms sX n m}
    (hτ : τ ≠ 0) : pullbackRationalPluriForms sX f τ ≠ 0 := by
  let := functionFieldAlgebra sX
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_genericPoint_mem_smoothLocus hη f hf hd
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := pullbackForms_eq hω m τ ▸ h0
  have h1 : algebraMap X.functionField Y.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← repr_pullbackFormsAlong hω m τ, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

/-- **The order of a pull-back along a basis.** Let `f : Y ⟶ X` be a dominant morphism of
integral schemes over `k` inducing an isomorphism of function fields, `X` of dimension `n` with
smooth generic point, and `E` a prime divisor of the normal scheme `Y` with smooth generic point.
There are a basis `b` of `Ω^n_{k(X)/k}` and an integer `N` with
`ord_E(f^*τ) = v_E(f^*(τ / b^{⊗m})) + m · N` for every `m` and every nonzero `τ`. -/
private theorem exists_ordForm_pullback_eq [IsIntegral X] [LocallyOfFiniteType sX]
    (hη : genericPoint X ∈ smoothLocus sX) {n : ℕ} (hn : topologicalKrullDim X = n)
    {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ X)
    [IsDominant f] [LocallyOfFiniteType (f ≫ sX)] (hf : Function.Bijective (functionFieldMap f))
    (E : MMP.Mori.PrimeDivisor Y) (hE : E.genericPoint ∈ smoothLocus (f ≫ sX)) :
    letI := functionFieldAlgebra sX
    ∃ (b : Module.Basis Unit X.functionField (⋀[X.functionField]^n Ω[X.functionField⁄k]))
      (N : ℤ), ∀ (m : ℤ) (τ : RationalPluriForms sX n m), τ ≠ 0 →
        pullbackRationalPluriForms sX f τ ≠ 0 ∧
        E.ordForm (pullbackRationalPluriForms sX f τ) =
          Y.ord (functionFieldMap f ((ZTensorPower.basis b m).repr τ ())) E.genericPoint +
            m * N := by
  let := functionFieldAlgebra sX
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_genericPoint_mem_smoothLocus hη f hf hd
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  have hdY : (Algebra.trdeg k Y.functionField).toNat = n := by
    rwa [← trdeg_functionField_eq_of_bijective sX f hf]
  obtain ⟨N, hN⟩ := exists_ordForm_eq_ord_add_mul_of_mem_smoothLocus (sX := f ≫ sX) E hE hdY
    (basisOfSpanSingleton hω.2.1 hω.2.2)
  refine ⟨basisOfSpanSingleton hω.1 hω.ne_zero, N, fun m τ hτ => ?_⟩
  have hpull : pullbackRationalPluriForms sX f τ = pullbackFormsAlong hω m τ :=
    pullbackForms_eq hω m τ
  have hne := pullbackRationalPluriForms_ne_zero hη hn f hf hτ
  refine ⟨hne, ?_⟩
  rw [hN m _ hne, hpull, repr_pullbackFormsAlong hω m τ]
  rfl

/-- **A local equation of `m'(K + Δ)` against forms has order zero.** Let `b` be a basis of
`Ω^n_{k(X)/k}`, `ω = c b` with `div(ω) = K`, `τ = c' b^{⊗m}` with `ord_Γ(τ) + m Δ_Γ = 0`, and `g`
with `v_Γ(g) = coeff_Γ(E)` for `E = m'(K + Δ)`, at a prime divisor `Γ` with smooth generic point.
Then `v_Γ(g^m c'^{m'} c^{-mm'}) = 0`. -/
private theorem ord_mul_zpow_eq_zero [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [LocallyOfFiniteType sX] {n : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = n)
    (b : letI := functionFieldAlgebra sX
      Module.Basis Unit X.functionField (⋀[X.functionField]^n Ω[X.functionField⁄k]))
    {K : Divisor X} {Δ : QDivisor X} {ω : RationalPluriForms sX n 1} (hω0 : ω ≠ 0)
    (hωK : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.ordForm ω = K.coeff Γ) {m : ℕ}
    {τ : RationalPluriForms sX n m} (hτ0 : τ ≠ 0) {m' : ℕ} {E : Divisor X}
    (hE : Divisor.toQDivisor E = (m' : ℤ) • (Divisor.toQDivisor K + Δ)) {g : X.functionField}
    (hg : g ≠ 0) (Γ : MMP.Mori.PrimeDivisor X) (hΓ : Γ.genericPoint ∈ smoothLocus sX)
    (e1 : (Γ.ordForm τ : ℚ) + m * Δ.coeff Γ = 0) (e4 : E.coeff Γ = X.ord g Γ.genericPoint) :
    letI := functionFieldAlgebra sX
    X.ord (g ^ (m : ℤ) * ((ZTensorPower.basis b (m : ℤ)).repr τ ()) ^ (m' : ℤ) *
      ((ZTensorPower.basis b 1).repr ω ()) ^ (-((m : ℤ) * m'))) Γ.genericPoint = 0 := by
  let := functionFieldAlgebra sX
  set c := (ZTensorPower.basis b 1).repr ω () with hc_def
  set c' := (ZTensorPower.basis b (m : ℤ)).repr τ () with hc'_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hω0
  have hc' : c' ≠ 0 := repr_ne_zero_of_ne_zero b hτ0
  obtain ⟨NΓ, hNΓ⟩ := exists_ordForm_eq_ord_add_mul_of_mem_smoothLocus Γ hΓ hd b
  have e2 := hNΓ (m : ℤ) τ hτ0
  have e3 := hNΓ 1 ω hω0
  have e5 : (E.coeff Γ : ℚ) = m' * (K.coeff Γ + Δ.coeff Γ) := by
    simpa [zsmul_eq_mul, mul_add] using congrArg (fun D : QDivisor X => D.coeff Γ) hE
  rw [Scheme.ord_mul (mul_ne_zero (zpow_ne_zero _ hg) (zpow_ne_zero _ hc'))
    (zpow_ne_zero _ hc), Scheme.ord_mul (zpow_ne_zero _ hg) (zpow_ne_zero _ hc'),
    ord_zpow _ hg, ord_zpow _ hc', ord_zpow _ hc]
  rw [← hωK Γ] at e5
  qify at e2 e3 e4 ⊢
  rw [← hc_def] at e3
  rw [← hc'_def] at e2
  simp only [zpow_one, one_mul] at e3
  rw [e4] at e5
  linear_combination (m : ℚ) * e5 + (m' : ℚ) * e1 - (m' : ℚ) * e2 + ((m : ℚ) * m') * e3

/-- **The discrepancy computes the pull-back of `K + Δ`** (KM 2.26, coefficientwise). Let
`f : Y ⟶ X` be a birational morphism of normal varieties, `X` smooth in codimension one and at
its generic point, `K = div(ω)` a canonical divisor, `F` a prime divisor of `Y` with smooth
generic point and `a = a(F, X, Δ)` its discrepancy. If `E = m'(K + Δ)` is a Cartier divisor with
pull-back `E'`, then `coeff_F(E') = m' (coeff_F(div(f^*ω)) - a)`.

With `τ = c' b^{⊗m}` generating `𝒪_X(m(K + Δ))` near `x = f(η_F)`, `ω = c b` and `φ` a local
equation of `E` at `x`, the rational function `φ^m c'^{m'} c^{-mm'}` has order zero along every
prime divisor through `x`, so is a unit at `x` (algebraic Hartogs) and its pull-back has order
zero along `F`. -/
private theorem coeff_isPullback_of_isDiscrepancy [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (hsmX : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.genericPoint ∈ smoothLocus sX)
    (hη : genericPoint X ∈ smoothLocus sX) {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X} [IsDominant f] [LocallyOfFiniteType (f ≫ sX)]
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) {n : ℕ} {K : Divisor X}
    {Δ : QDivisor X} {ω : RationalPluriForms sX n 1} (hω0 : ω ≠ 0)
    (hωK : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.ordForm ω = K.coeff Γ) (F : MMP.Mori.PrimeDivisor Y)
    (hF : F.genericPoint ∈ smoothLocus (f ≫ sX)) {a : ℚ}
    (hdisc : IsDiscrepancy sX n K Δ ⟨Y, f, hY, hf, F⟩ a) {m' : ℕ} {E : Divisor X}
    (hE : Divisor.toQDivisor E = (m' : ℤ) • (Divisor.toQDivisor K + Δ)) (hEc : E.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ E.supp}
    {E' : Divisor Y} (hE' : E.IsPullback f hB E') :
    (E'.coeff F : ℚ) =
      m' * ((divisorOfForm (pullbackRationalPluriForms sX f ω)).coeff F - a) := by
  obtain ⟨hX, hK, m, hm, -, U, hU, τ, hτ, hτa⟩ := hdisc
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  let := functionFieldAlgebra sX
  have hn := hK.topologicalKrullDim_eq
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨b, N', hb⟩ := exists_ordForm_pullback_eq hη hn f hf.functionFieldMap_bijective F hF
  obtain ⟨V, hxV, φ, hφ⟩ := hEc (f F.genericPoint)
  have hsub := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)
  let Z0 : irreducibleComponents X := ⟨Set.univ, by
    rw [irreducibleComponents_eq_singleton]; simp⟩
  set c := (ZTensorPower.basis b 1).repr ω () with hc_def
  set c' := (ZTensorPower.basis b (m : ℤ)).repr τ () with hc'_def
  set g := MMP.Threefold.Mori.Helpers.evalFF Z0 (φ : RationalFunctions X) with hg_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hω0
  have hc' : c' ≠ 0 := repr_ne_zero_of_ne_zero b hτ.1
  have hg : g ≠ 0 := (φ.isUnit.map _).ne_zero
  set G : X.functionField := g ^ (m : ℤ) * c' ^ (m' : ℤ) * c ^ (-((m : ℤ) * m')) with hG_def
  have hG : G ≠ 0 :=
    mul_ne_zero (mul_ne_zero (zpow_ne_zero _ hg) (zpow_ne_zero _ hc')) (zpow_ne_zero _ hc)
  have hord : ∀ Γ : MMP.Mori.PrimeDivisor X, f F.genericPoint ∈ Γ.support →
      X.ord G Γ.genericPoint = 0 := fun Γ hΓ =>
    ord_mul_zpow_eq_zero hd b hω0 hωK hτ.1 hE hg Γ (hsmX Γ) (hτ.2 Γ ⟨_, hΓ, hU⟩) (by
      rw [hφ Γ ⟨_, hΓ, hxV⟩, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord,
        Subsingleton.elim Γ.component Z0])
  obtain ⟨u', hu', hug⟩ := exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero _ hG hord
  have hY0 : Y.ord (functionFieldMap f G) F.genericPoint = 0 := by
    rw [← hug, functionFieldMap_algebraMap_stalk]
    exact F.ord_algebraMap_of_isUnit (hu'.map _)
  have hfg : functionFieldMap f g ≠ 0 := (map_ne_zero _).mpr hg
  have hfc : functionFieldMap f c ≠ 0 := (map_ne_zero _).mpr hc
  have hfc' : functionFieldMap f c' ≠ 0 := (map_ne_zero _).mpr hc'
  rw [hG_def, map_mul, map_mul, map_zpow₀, map_zpow₀, map_zpow₀,
    Scheme.ord_mul (mul_ne_zero (zpow_ne_zero _ hfg) (zpow_ne_zero _ hfc')) (zpow_ne_zero _ hfc),
    Scheme.ord_mul (zpow_ne_zero _ hfg) (zpow_ne_zero _ hfc'), ord_zpow _ hfg, ord_zpow _ hfc',
    ord_zpow _ hfc] at hY0
  have hτa' : (m : ℚ) * a = F.ordForm (pullbackRationalPluriForms sX f τ) := hτa
  rw [(hb (m : ℤ) τ hτ.1).2, ← hc'_def] at hτa'
  rw [coeff_divisorOfForm, (hb 1 ω hω0).2, ← hc_def,
    MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hE' hφ F hxV Z0]
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  apply mul_left_cancel₀ hm0
  qify at hY0
  push_cast at hτa' ⊢
  linear_combination hY0 + (m' : ℚ) * hτa'

/-- **Divisors of top forms are linearly equivalent** on a normal variety smooth in codimension
one: `div(τ) - div(ω) = div(τ / ω)`. -/
private theorem linearlyEquivalent_divisorOfForm [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX)
    (hsm : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.genericPoint ∈ smoothLocus sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {τ ω : RationalPluriForms sX n 1} (hτ : τ ≠ 0)
    (hω : ω ≠ 0) : Divisor.LinearlyEquivalent (divisorOfForm τ) (divisorOfForm ω) := by
  let := functionFieldAlgebra sX
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  let b := Module.basisUnique Unit
    (MMP.Positivity.finrank_topForms_functionField_eq_one hX hsm hn)
  set c := (ZTensorPower.basis b 1).repr ω () with hc_def
  set e := (ZTensorPower.basis b 1).repr τ () with he_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hω
  have he : e ≠ 0 := repr_ne_zero_of_ne_zero b hτ
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero (mul_ne_zero he (inv_ne_zero hc))
  refine ⟨φ, ?_⟩
  ext Γ
  obtain ⟨N, hN⟩ := exists_ordForm_eq_ord_add_mul_of_mem_smoothLocus Γ (hsm Γ) hd b
  have e1 := hN 1 ω hω
  have e2 := hN 1 τ hτ
  rw [← hc_def] at e1
  rw [← he_def] at e2
  rw [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor, hφ Γ,
    Scheme.ord_mul he (inv_ne_zero hc), ← zpow_neg_one, ord_zpow _ hc, coeff_divisorOfForm,
    coeff_divisorOfForm, e1, e2]
  ring

/-- At the generic point a birational morphism of integral schemes induces an isomorphism of
local rings, so a smooth generic point of the source gives a smooth generic point of the
target. -/
private theorem genericPoint_mem_smoothLocus_of_isBirationalMorphism [IsIntegral X]
    [LocallyOfFiniteType sX] {Y : Scheme.{0}} [IsIntegral Y] {f : Y ⟶ X}
    [LocallyOfFiniteType (f ≫ sX)] (hf : IsBirationalMorphism f)
    (hη : genericPoint Y ∈ smoothLocus (f ≫ sX)) : genericPoint X ∈ smoothLocus sX := by
  have : IsDominant f := hf.isDominant
  have : ValuationRing (X.presheaf.stalk (f (genericPoint Y))) := by
    rw [map_genericPoint_of_isDominant]
    exact (inferInstance : ValuationRing X.functionField)
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf.functionFieldMap_bijective
    (genericPoint Y)
  have h := map_mem_smoothLocus_of_isIso_stalkMap f hη
  rwa [map_genericPoint_of_isDominant] at h

/-- **The crepant boundary computes the pull-back** (KM 2.26). For a birational morphism
`f : Y ⟶ X` of normal varieties with `X` smooth in codimension one and at its generic point, `Y`
smooth in codimension one, `K = div(ω)` and `Δ_Y` the crepant boundary of `(X, Δ)` on `Y`,
`div(f^*ω) + Δ_Y = f^*(K + Δ)`. -/
private theorem isPullback_divisorOfForm_add_of_isCrepantBoundary [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X]
    (hsmX : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.genericPoint ∈ smoothLocus sX)
    (hη : genericPoint X ∈ smoothLocus sX) {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X} [IsDominant f] [LocallyOfFiniteType (f ≫ sX)]
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    (hsmY : ∀ F : MMP.Mori.PrimeDivisor Y, F.genericPoint ∈ smoothLocus (f ≫ sX)) {n : ℕ}
    {K : Divisor X} {Δ : QDivisor X} {ω : RationalPluriForms sX n 1} (hω0 : ω ≠ 0)
    (hωK : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.ordForm ω = K.coeff Γ) {ΔY : QDivisor Y}
    (hcrep : IsCrepantBoundary sX n K Δ f hY hf ΔY)
    (hB : ∀ Z : irreducibleComponents Y,
      f (componentGenericPoint Y Z) ∉ (Divisor.toQDivisor K + Δ).supp) :
    (Divisor.toQDivisor K + Δ).IsPullback f hB
      (Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms sX f ω)) + ΔY) := by
  intro m' hm' E hE hEc
  have hB' : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ E.supp :=
    map_componentGenericPoint_notMem_supp f E
  refine ⟨E.pullback hEc hB', ?_, Divisor.isPullback_pullback hEc _⟩
  ext F
  have h := coeff_isPullback_of_isDiscrepancy hsmX hη hY hf hω0 hωK F (hsmY F) (hcrep F) hE hEc
    (Divisor.isPullback_pullback hEc hB')
  simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, zsmul_eq_mul,
    Divisor.coeff_toQDivisor, Int.cast_natCast]
  rw [h]
  ring

end Forms

/-- The divisor `∑_j r_j F_j` read as a `ℚ`-divisor. -/
private theorem toQDivisor_sum_single {Y : Scheme.{0}} {ι : Type*} [Fintype ι]
    (F : ι → MMP.Mori.PrimeDivisor Y) (r : ι → ℕ) :
    Divisor.toQDivisor (∑ j, Finsupp.single (F j) (r j : ℤ)) =
      ∑ j, Finsupp.single (F j) (r j : ℚ) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ext G
  classical
  change ((Finsupp.single (F j) (r j : ℤ) : Divisor Y) G : ℚ) =
    (Finsupp.single (F j) (r j : ℚ) : QDivisor Y) G
  rw [Finsupp.single_apply, Finsupp.single_apply]
  split_ifs <;> simp

/-- The round-down of a `ℚ`-divisor with integral coefficients is the divisor itself. -/
private theorem roundDown_toQDivisor {X : Scheme.{0}} (D : Divisor X) :
    (Divisor.toQDivisor D).roundDown = D := by
  ext E
  change ((Divisor.toQDivisor D).roundDown).coeff E = D.coeff E
  rw [DivisorWithCoeffs.coeff_roundDown, Divisor.coeff_toQDivisor, Int.floor_intCast]

/-- **The numerics of the test divisor.** If `0 < a`, `0 < c`, `0 ≤ r`, `aq - rp > 0`,
`p' ≥ (1 + c) p`, `q' ≥ (1 + c) q` and `aq' - rp' ≤ aq - rp`, then `x = p' - (1 + c) p` and
`t = (q' - (1 + c) q) a` satisfy `0 < x` and `0 ≤ t < r x`: indeed
`t - r x = (aq' - rp') - (1 + c)(aq - rp) ≤ -c (aq - rp) < 0`. -/
private theorem pos_and_nonneg_and_lt_mul {a p q p' q' : ℤ} {c : ℚ} {r : ℝ} (ha : (0 : ℚ) < a)
    (hc : 0 < c) (hr : 0 ≤ r) (hpq : 0 < (a * q : ℝ) - r * p) (hp' : (1 + c) * p ≤ p')
    (hq' : (1 + c) * q ≤ q') (hpq' : (a * q' : ℝ) - r * p' ≤ a * q - r * p) :
    0 < (p' - (1 + c) * p : ℚ) ∧ 0 ≤ ((q' - (1 + c) * q) * a : ℚ) ∧
      (((q' - (1 + c) * q) * a : ℚ) : ℝ) < r * ((p' - (1 + c) * p : ℚ) : ℝ) := by
  have ht0 : 0 ≤ ((q' - (1 + c) * q) * a : ℚ) := mul_nonneg (by linarith) ha.le
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hrx : (((q' - (1 + c) * q) * a : ℚ) : ℝ) < r * ((p' - (1 + c) * p : ℚ) : ℝ) := by
    push_cast
    nlinarith
  refine ⟨lt_of_not_ge fun hx => ?_, ht0, hrx⟩
  have : r * ((p' - (1 + c) * p : ℚ) : ℝ) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hr (by exact_mod_cast hx)
  have : (0 : ℝ) ≤ (((q' - (1 + c) * q) * a : ℚ) : ℝ) := by exact_mod_cast ht0
  linarith

/-- **The test boundary minus `F_{j₀}`.** If `-c r_{j₀} + a_{j₀} - p_{j₀} = -1`, then
`∑_{j ≠ j₀} (-c r_j + a_j - p_j) F_j - F_{j₀} = ∑_j a_j F_j - ∑_j p_j F_j - c ∑_j r_j F_j`. -/
private theorem tieBreakerBoundary_sub_single_eq {Y : Scheme.{0}} {s : ℕ}
    (F : Fin s → MMP.Mori.PrimeDivisor Y) (aj pj : Fin s → ℚ) (rj : Fin s → ℕ) {j₀ : Fin s}
    {c : ℚ} (hcj₀ : -c * (rj j₀ : ℚ) + aj j₀ - pj j₀ = -1) :
    tieBreakerBoundary F (fun j => (rj j : ℚ)) aj pj j₀ c - Finsupp.single (F j₀) 1 =
      (∑ j, Finsupp.single (F j) (aj j) : QDivisor Y) - ∑ j, Finsupp.single (F j) (pj j) -
        c • ∑ j, Finsupp.single (F j) (rj j : ℚ) := by
  have h1 : tieBreakerBoundary F (fun j => (rj j : ℚ)) aj pj j₀ c - Finsupp.single (F j₀) 1 =
      ∑ j, Finsupp.single (F j) (-c * (rj j : ℚ) + aj j - pj j) := by
    rw [tieBreakerBoundary, ← Finset.add_sum_erase _ _ (Finset.mem_univ j₀), hcj₀,
      Finsupp.single_neg]
    abel
  rw [h1, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.smul_single, ← Finsupp.single_sub, ← Finsupp.single_sub, smul_eq_mul]
  congr 1
  ring

/-- On a scheme all of whose `ℚ`-divisors are `ℚ`-Cartier, `c L + L'` is nef for nef `L, L'`
and `0 ≤ c`. -/
private theorem isNef_smul_add_of_forall_isQCartier {k : Type} [Field k] {W : Scheme.{0}}
    [IsLocallyNoetherian W] [IsNormal W] {sW : W ⟶ Spec (.of k)} [QuasiCompact sW]
    (hQ : ∀ L : QDivisor W, L.IsQCartier) {c : ℚ} (hc : 0 ≤ c) {L L' : QDivisor W}
    (hL : L.IsNef k sW) (hL' : L'.IsNef k sW) : (c • L + L').IsNef k sW := by
  refine ⟨hQ _, fun C i _ _ _ hC => ?_⟩
  rw [← intersectionLinearMap_apply sW i hC.le hQ (c • L + L') (hQ _), map_add, map_smul,
    smul_eq_mul, intersectionLinearMap_apply sW i hC.le hQ _ hL.1,
    intersectionLinearMap_apply sW i hC.le hQ _ hL'.1]
  exact add_nonneg (mul_nonneg hc (hL.2 C i hC)) (hL'.2 C i hC)

/-- **`f^*(K_X + Δ) = K_Y + Δ_Y` up to linear equivalence** (KM 2.26). For a smooth projective
birational `f : Y ⟶ X` of normal varieties, a canonical divisor `K_Y` of `Y` and the crepant
boundary `Δ_Y` of `(X, Δ)` on `Y`, some `K'_Y ∼ K_Y` has `f^*(K_X + Δ) = K'_Y + Δ_Y`. -/
private theorem exists_isPullback_add_linearlyEquivalent {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {Δ : QDivisor X} {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] {f : Y ⟶ X} [IsProper f] (hY : IsNormalVariety k (f ≫ sX))
    (hf : IsBirationalMorphism f) (hsm : IsSmoothScheme (f ≫ sX)) {ΔY : QDivisor Y}
    (hcrep : IsCrepantBoundary sX n K Δ f hY hf ΔY) {KY : Divisor Y}
    (hKY : KY.IsCanonicalDivisor (f ≫ sX) n) :
    ∃ (hB : ∀ Z : irreducibleComponents Y,
        f (componentGenericPoint Y Z) ∉ (Divisor.toQDivisor K + Δ).supp) (KY' : Divisor Y),
      (Divisor.toQDivisor K + Δ).IsPullback f hB (Divisor.toQDivisor KY' + ΔY) ∧
        (KY' - KY).LinearlyEquivalent 0 := by
  have : IsDominant f := hf.isDominant
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  have htop : smoothLocus (f ≫ sX) = ⊤ := hsm
  have hsmX := genericPoint_mem_smoothLocus_of_isSmoothScheme hX hY hf hsm
  have hsmY : ∀ F : MMP.Mori.PrimeDivisor Y, F.genericPoint ∈ smoothLocus (f ≫ sX) := by
    rw [htop]
    exact fun _ => trivial
  have hηY : genericPoint Y ∈ smoothLocus (f ≫ sX) := by
    rw [htop]
    trivial
  have hη := genericPoint_mem_smoothLocus_of_isBirationalMorphism hf hηY
  obtain ⟨ω, hω0, hωK⟩ :=
    MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq_of_forall_mem_smoothLocus hX hsmX hK
  obtain ⟨ωY, hωY0, hωYK⟩ :=
    MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq_of_forall_mem_smoothLocus hY hsmY hKY
  have hKYeq : KY = divisorOfForm ωY := by
    ext G
    exact (hωYK G).symm
  obtain ⟨φ, hφ⟩ := linearlyEquivalent_divisorOfForm hY hsmY hKY.1
    (pullbackRationalPluriForms_ne_zero hη hK.1 f hf.functionFieldMap_bijective hω0) hωY0
  exact ⟨_, _, isPullback_divisorOfForm_add_of_isCrepantBoundary hsmX hη hY hf hsmY hω0 hωK
    hcrep (map_componentGenericPoint_notMem_supp f _), ⟨φ, by rw [sub_zero, hKYeq, hφ]⟩⟩

/-- **The correction term is nef.** With `x = p' - (1 + c) p` and `t = (q' - (1 + c) q) a`, the
`ℚ`-divisor `xH + t(K_X + Δ)` is nef, and so is a pull-back of it to `Y`. -/
private theorem exists_isPullback_isNef_of_isStripTieBreaker {k : Type} [Field k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {a : ℤ}
    {H : Divisor X} {p q : ℤ} {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] {f : Y ⟶ X} {s : ℕ} {F : Fin s → MMP.Mori.PrimeDivisor Y}
    {aj pj : Fin s → ℚ} {rj : Fin s → ℕ} {j₀ : Fin s} {c : ℚ}
    (h : IsStripTieBreaker sX n K Δ a H p q f F aj pj rj j₀ c) {r : ℝ}
    (hr : QDivisor.IsNefThreshold k sX (Divisor.toQDivisor H) (Divisor.toQDivisor K + Δ) r)
    (hpq : 0 < (a * q : ℝ) - r * p) {p' q' : ℤ} (hp' : (1 + c) * p ≤ p')
    (hq' : (1 + c) * q ≤ q') (hpq' : (a * q' : ℝ) - r * p' ≤ a * q - r * p) (hc : 0 < c) :
    ∃ (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉
        ((p' - (1 + c) * p : ℚ) • Divisor.toQDivisor H +
          ((q' - (1 + c) * q) * a : ℚ) • (Divisor.toQDivisor K + Δ)).supp) (W : QDivisor Y),
      ((p' - (1 + c) * p : ℚ) • Divisor.toQDivisor H +
          ((q' - (1 + c) * q) * a : ℚ) • (Divisor.toQDivisor K + Δ)).IsPullback f hB W ∧
        W.IsNef k (f ≫ sX) := by
  obtain ⟨hYn, -⟩ := h.isCrepantBoundary
  have : IsProper f := h.isLogResolution.isProper
  have : AlgebraicGeometry.IsProjectiveVariety k (f ≫ sX) := h.isProjectiveVariety
  have : AlgebraicGeometry.IsProperVariety k sX := h.isProperVariety
  have : IsIntegral Y := hYn.1.toIsIntegral
  have : IsDominant f := h.isLogResolution.isBirationalMorphism.isDominant
  obtain ⟨hHq, hPq, -⟩ := hr.1
  have hr0 : 0 ≤ r := not_lt.1 fun hr0 => hr.2 0 hr0 ⟨hHq, hPq, fun C i _ _ _ hC => by
    rw [zero_mul, add_zero]
    exact_mod_cast ((QDivisor.isNef_toQDivisor_iff H h.isCartier_H).mpr h.isNef_H).2 C i hC⟩
  obtain ⟨hx, ht0, hrx⟩ :=
    pos_and_nonneg_and_lt_mul (by exact_mod_cast h.pos) hc hr0 hpq hp' hq' hpq'
  have hWX : ((p' - (1 + c) * p : ℚ) • Divisor.toQDivisor H +
      ((q' - (1 + c) * q) * a : ℚ) • (Divisor.toQDivisor K + Δ)).IsNef k sX :=
    isNef_add_smul_of_isNefCombination
      (MMP.Positivity.IsRationalityDatum.isNefCombination_of_le h.toIsRationalityDatum hr hx
        (by exact_mod_cast ht0) hrx.le)
  have hWp := QDivisor.isPullback_pullback hWX.1 (map_componentGenericPoint_notMem_supp f _)
  exact ⟨_, _, hWp, isNef_of_isPullback rfl hWX hWp⟩

/-- **The numerical class of the test divisor.** If
`N = f^*(p'H + q'aP) + ∑_j a_j F_j - ∑_j p_j F_j - c ∑_j r_j F_j - K_Y` with
`f^*P = K'_Y - ∑_j a_j F_j` and `K'_Y ∼ K_Y`, then
`N ≡ (f^*(pH + (qa - 1)P) - ∑_j p_j F_j) + (c (f^*M - ∑_j r_j F_j) + f^*(xH + tP))` for
`M = pH + qaP`, `x = p' - (1 + c) p` and `t = (q' - (1 + c) q) a`. -/
private theorem numericallyEquivalent_add_of_isPullback {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [AlgebraicGeometry.IsProperVariety k sX]
    {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {f : Y ⟶ X} [IsProper f] [AlgebraicGeometry.IsProjectiveVariety k (f ≫ sX)]
    (hQ : ∀ L : QDivisor Y, L.IsQCartier) (hcart : ∀ L : Divisor Y, L.IsCartier)
    {H : Divisor X} {P : QDivisor X} (hHq : (Divisor.toQDivisor H).IsQCartier)
    (hPq : P.IsQCartier) {M : Divisor X} {a p q p' q' : ℤ} {c x t : ℚ}
    (hMQ : Divisor.toQDivisor M = (p : ℚ) • Divisor.toQDivisor H + ((q * a : ℤ) : ℚ) • P)
    (hx : x = p' - (1 + c) * p) (ht : t = (q' - (1 + c) * q) * a)
    {H' KY' KY M' Rd : Divisor Y} {Sa Sp Sr B' B'' W N : QDivisor Y}
    {hH : ∀ Z : irreducibleComponents Y,
      f (componentGenericPoint Y Z) ∉ (Divisor.toQDivisor H).supp}
    (hH'p : (Divisor.toQDivisor H).IsPullback f hH (Divisor.toQDivisor H'))
    {hP : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ P.supp}
    (hP'p : P.IsPullback f hP (Divisor.toQDivisor KY' + -Sa))
    {hM : ∀ Z : irreducibleComponents Y,
      f (componentGenericPoint Y Z) ∉ (Divisor.toQDivisor M).supp}
    (hM'p : (Divisor.toQDivisor M).IsPullback f hM (Divisor.toQDivisor M'))
    {hB₁ : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉
      (p • Divisor.toQDivisor H + (q * a - 1) • P).supp}
    (hB'p : (p • Divisor.toQDivisor H + (q * a - 1) • P).IsPullback f hB₁ B')
    {hB₂ : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉
      (p' • Divisor.toQDivisor H + (q' * a) • P).supp}
    (hB''p : (p' • Divisor.toQDivisor H + (q' * a) • P).IsPullback f hB₂ B'')
    {hW : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉
      (x • Divisor.toQDivisor H + t • P).supp}
    (hWp : (x • Divisor.toQDivisor H + t • P).IsPullback f hW W)
    (hKYlin : (KY' - KY).LinearlyEquivalent 0) (hRd : Divisor.toQDivisor Rd = Sr)
    (hN : N = B'' + (Sa - Sp - c • Sr) - Divisor.toQDivisor KY) :
    N.NumericallyEquivalent k (f ≫ sX)
      ((B' - Sp) + ∑ _i ∈ ({()} : Finset Unit), (c • Divisor.toQDivisor (M' - Rd) + W)) := by
  refine ⟨hQ _, hQ _, fun C i _ _ _ hC => ?_⟩
  have : AlgebraicGeometry.IsCurve k (i ≫ f ≫ sX) := { topologicalKrullDim_eq_one := hC }
  set ι := intersectionLinearMap (f ≫ sX) i hC.le hQ with hι
  have k1 : ι B' = (p : ℚ) * ι (Divisor.toQDivisor H') +
      ((q * a - 1 : ℤ) : ℚ) * ι (Divisor.toQDivisor KY' + -Sa) :=
    intersectionNumber_isPullback_smul_add_smul (sV := f ≫ sX) (sW := sX) rfl i hHq hPq
      (p : ℚ) ((q * a - 1 : ℤ) : ℚ) (by rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul])
      hB'p hH'p hP'p (hQ _) (hQ _) (hQ _)
  have k2 : ι B'' = (p' : ℚ) * ι (Divisor.toQDivisor H') +
      ((q' * a : ℤ) : ℚ) * ι (Divisor.toQDivisor KY' + -Sa) :=
    intersectionNumber_isPullback_smul_add_smul (sV := f ≫ sX) (sW := sX) rfl i hHq hPq
      (p' : ℚ) ((q' * a : ℤ) : ℚ) (by rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul])
      hB''p hH'p hP'p (hQ _) (hQ _) (hQ _)
  have k3 : ι (Divisor.toQDivisor M') = (p : ℚ) * ι (Divisor.toQDivisor H') +
      ((q * a : ℤ) : ℚ) * ι (Divisor.toQDivisor KY' + -Sa) :=
    intersectionNumber_isPullback_smul_add_smul (sV := f ≫ sX) (sW := sX) rfl i hHq hPq
      (p : ℚ) ((q * a : ℤ) : ℚ) hMQ hM'p hH'p hP'p (hQ _) (hQ _) (hQ _)
  have k4 : ι W = x * ι (Divisor.toQDivisor H') + t * ι (Divisor.toQDivisor KY' + -Sa) :=
    intersectionNumber_isPullback_smul_add_smul (sV := f ≫ sX) (sW := sX) rfl i hHq hPq
      x t rfl hWp hH'p hP'p (hQ _) (hQ _) (hQ _)
  have k5 : ι (Divisor.toQDivisor KY') = ι (Divisor.toQDivisor KY) := by
    have e1 : ι (Divisor.toQDivisor (KY' - KY)) = 0 := by
      rw [hι, intersectionLinearMap_apply (f ≫ sX) i hC.le hQ _
          (QDivisor.isQCartier_toQDivisor (hcart _)),
        QDivisor.intersectionNumber_toQDivisor k (f ≫ sX) i hC.le _ (hcart _),
        MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent (f ≫ sX) i hC.le (hcart _)
          hKYlin, Int.cast_zero]
    rw [map_sub, map_sub] at e1
    linarith
  rw [← intersectionLinearMap_apply (f ≫ sX) i hC.le hQ N (hQ _),
    ← intersectionLinearMap_apply (f ≫ sX) i hC.le hQ _ (hQ _), ← hι, Finset.sum_singleton, hN,
    show Divisor.toQDivisor (M' - Rd) = Divisor.toQDivisor M' - Sr by rw [map_sub, hRd]]
  rw [hx, ht] at k4
  simp only [map_add, map_sub, map_neg, map_smul, smul_eq_mul] at k1 k2 k3 k4 ⊢
  push_cast at k1 k2 k3 k4
  linear_combination k2 - k1 - c * k3 - k4 + k5

end MMP.FourfoldProofs.Km3bStripTestDivisorAmpleProof

end

section

/-! ### The main theorem -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori

open MMP.FourfoldProofs.Km3bStripTestDivisorAmpleProof in
/-- **The test divisors are ample** (Kollár–Mori 3.4, Step 8). Let `(X, Δ, a, H)` be a
rationality datum with nef threshold `r` of `H` with respect to `K_X + Δ`, `p, q > 0` integers
with `0 < aq - rp`, and `(j₀, c)` a tie-breaker of a `(p, q)`-adapted resolution
`(f; F_•; a_•; p_•; r_•)`. Then for integers `p', q'` with `(1 + c) p ≤ p'`, `(1 + c) q ≤ q'`
and `aq' - rp' ≤ aq - rp`, the test divisor
`N(p', q') = f^*(p'H + q'a(K_X + Δ)) + A' - F_{j₀} - K_Y` is ample. -/
@[mmp "lem_km3b_strip_test_divisor_ample"]
public theorem IsStripTieBreaker.isAmple_of_isStripTestDivisor
    {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {a : ℤ} {H : Divisor X} {p q : ℤ}
    {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X}
    {s : ℕ} {F : Fin s → PrimeDivisor Y} {aj pj : Fin s → ℚ} {rj : Fin s → ℕ}
    {j₀ : Fin s} {c : ℚ} (h : IsStripTieBreaker sX n K Δ a H p q f F aj pj rj j₀ c) {r : ℝ}
    (hr : QDivisor.IsNefThreshold k sX (Divisor.toQDivisor H) (Divisor.toQDivisor K + Δ) r)
    (hpq : 0 < (a * q : ℝ) - r * p) {p' q' : ℤ} (hp' : (1 + c) * p ≤ p') (hq' : (1 + c) * q ≤ q')
    (hpq' : (a * q' : ℝ) - r * p' ≤ a * q - r * p) {KY : Divisor Y} {N : QDivisor Y}
    (hN : IsStripTestDivisor sX n K Δ a H f KY F aj pj rj j₀ c p' q' N) :
    N.IsAmple := by
  obtain ⟨hKY, hBN, B'', hB''p, hNeq⟩ := hN
  obtain ⟨hYn, hcrep⟩ := h.isCrepantBoundary
  have hLR := h.isLogResolution
  have hsm : IsSmoothScheme (f ≫ sX) := hLR.isSmoothScheme
  have : IsProper f := hLR.isProper
  have hfb : IsBirationalMorphism f := hLR.isBirationalMorphism
  have : AlgebraicGeometry.IsProjectiveVariety k (f ≫ sX) := h.isProjectiveVariety
  have : AlgebraicGeometry.IsProperVariety k sX := h.isProperVariety
  have : IsIntegral Y := hYn.1.toIsIntegral
  have : IsDominant f := hfb.isDominant
  have hQ : ∀ L : QDivisor Y, L.IsQCartier := MMP.Fourfold.isQCartier_of_isSmoothScheme hsm
  have hcart : ∀ L : Divisor Y, L.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm
  obtain ⟨hHq, hPq, -⟩ := hr.1
  set P : QDivisor X := Divisor.toQDivisor K + Δ
  obtain ⟨_, KY', hP'p, hKYlin⟩ := exists_isPullback_add_linearlyEquivalent h.isKltPair.1.1
    h.isKltPair.1.2.1 hYn hfb hsm hcrep hKY
  have hHc := h.isCartier_H
  have hH'p := QDivisor.isPullback_toQDivisor hHc (map_componentGenericPoint_notMem_supp f _)
    (Divisor.isPullback_pullback hHc (map_componentGenericPoint_notMem_supp f _))
  obtain ⟨D₀, hD₀, hD₀c⟩ := h.isCartierDivisor
  have hround : (a • P).roundDown = D₀ := by rw [← hD₀, roundDown_toQDivisor]
  set M : Divisor X := stripDivisor K Δ a H p q with hM_def
  have hMc : M.IsCartier := by
    rw [hM_def, stripDivisor, hround]
    exact (hHc.zsmul p).add (hD₀c.zsmul q)
  have hMQ : Divisor.toQDivisor M = (p : ℚ) • Divisor.toQDivisor H + ((q * a : ℤ) : ℚ) • P := by
    rw [hM_def, stripDivisor, hround, map_add, map_zsmul, map_zsmul, hD₀, smul_smul,
      Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  have hM'p := QDivisor.isPullback_toQDivisor hMc (map_componentGenericPoint_notMem_supp f _)
    (Divisor.isPullback_pullback hMc (map_componentGenericPoint_notMem_supp f _))
  set M' : Divisor Y := M.pullback hMc (map_componentGenericPoint_notMem_supp f _)
  set Rd : Divisor Y := ∑ j, Finsupp.single (F j) (rj j : ℤ)
  have hLnef : (Divisor.toQDivisor (M' - Rd)).IsNef k (f ≫ sX) :=
    isNef_sub_of_forall_exists_notMem_supp hcart hMc
      (Divisor.isPullback_pullback hMc (map_componentGenericPoint_notMem_supp f _)) Rd
      h.le_zeroDivisor h.exists_notMem_supp
  have hrj₀ : (0 : ℚ) < rj j₀ := by exact_mod_cast h.pos_r
  have hc : 0 < c := by
    rw [h.eq_div]
    exact div_pos (by linarith [h.lt_one_add j₀]) hrj₀
  have hcj₀ : -c * (rj j₀ : ℚ) + aj j₀ - pj j₀ = -1 := by
    rw [h.eq_div, neg_mul, div_mul_cancel₀ _ hrj₀.ne']
    ring
  obtain ⟨_, W, hWp, hWnef⟩ :=
    exists_isPullback_isNef_of_isStripTieBreaker h hr hpq hp' hq' hpq' hc
  obtain ⟨_, B', hB'p, hA⟩ := h.isAmple
  exact QDivisor.isAmple_of_numericallyEquivalent_add_sum_of_isNef (f ≫ sX) {()}
    (fun _ => c • Divisor.toQDivisor (M' - Rd) + W) hA
    (fun _ _ => isNef_smul_add_of_forall_isQCartier hQ hc.le hLnef hWnef)
    (numericallyEquivalent_add_of_isPullback (Sp := ∑ j, Finsupp.single (F j) (pj j)) hQ hcart
      hHq hPq hMQ rfl rfl hH'p hP'p hM'p hB'p hB''p hWp hKYlin (toQDivisor_sum_single F rj)
      (by rw [hNeq, add_sub_assoc B'', tieBreakerBoundary_sub_single_eq F aj pj rj hcj₀]))

end MMP.Mori

end

end
