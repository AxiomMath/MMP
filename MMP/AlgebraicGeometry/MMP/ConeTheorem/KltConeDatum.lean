module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.RationalityTheorem
public import MMP.AlgebraicGeometry.MMP.BasepointFree.ProofData
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Basic
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.Intersection.N1FiniteDimensionalProper
public import MMP.AlgebraicGeometry.Intersection.NumericalDivisorLattice
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.SupportingDivisorStein
public import MMP.AlgebraicGeometry.Positivity.Kleiman.AbsoluteCartier
public import MMP.AlgebraicGeometry.Positivity.NefBigOfAmpleApproximation
public import MMP.AlgebraicGeometry.Intersection.PairingSeparation
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
public import MMP.AlgebraicGeometry.Positivity.BaseLocusSum
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries

@[expose] public section

universe u

section

/-!
# The cone of curves of a klt pair is a cone datum

Let `X` be a projective variety over an algebraically closed field of characteristic zero and
`(X, Δ)` a klt pair with `Δ ≥ 0`, `K_X + Δ` not nef and `a(K_X + Δ)` Cartier. A `ℤ`-basis
`e₁, …, e_ρ` of `Num(X)` is an `ℝ`-basis of `N₁(X)^*`; its dual basis spans the lattice
`N₁(X)_ℤ` over `ℤ`, which gives freeness, `N₁(X)_ℤ ⊗ ℝ = N₁(X)` and `Hom(N₁(X)_ℤ, ℤ) = Num(X)`.
The cone `NE̅(X)` is closed and contains no line, and `K = (K_X + Δ · _)` is `1/m` times an
integral form, `m` the Cartier index. An integral form `H` positive on `NE̅(X) \ 0` is the
degree form of a Cartier divisor `D`, which is ample by Kleiman's criterion, hence nef and big;
the `K`-threshold of `H` on `NE̅(X)` is the nef threshold of `D` with respect to `K_X + Δ`, which
by the rationality theorem is `u / v` with `0 < v ≤ a(n + 1)`, so it lies in `(1/(a(n+1))!) ℤ`.

## Main results

* `MMP.Mori.exists_coneDatum_numericalCurveLattice_of_isKltPair`: the statement above.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.14
-/

namespace MMP.FourfoldProofs.Km3bConeHypothesesFromRationalityProof

open CategoryTheory AlgebraicGeometry TensorProduct Module MMP.Mori

section Lattice

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- Let `M ⊆ V^*` be a free abelian group of finite rank whose `ℤ`-bases are `ℝ`-bases of `V^*`,
and `Λ = {z ∈ V | φ(z) ∈ ℤ for all φ ∈ M}`. Then `Λ` is free of finite rank, `ℝ ⊗_ℤ Λ → V` is
bijective, and restriction identifies `M` with `Hom(Λ, ℤ)`. -/
private theorem lattice_facts (M : AddSubgroup (Dual ℝ V)) [Module.Free ℤ M] [Module.Finite ℤ M]
    (hbasis : ∀ {ι : Type u} (b : Basis ι ℤ M),
      LinearIndependent ℝ (fun i => (b i : Dual ℝ V)) ∧
        Submodule.span ℝ (Set.range fun i => (b i : Dual ℝ V)) = ⊤)
    (Λ : AddSubgroup V) (hΛ : ∀ z, z ∈ Λ ↔ ∀ φ ∈ M, ∃ n : ℤ, φ z = n) :
    Module.Free ℤ Λ ∧ Module.Finite ℤ Λ ∧
      Function.Bijective (LinearMap.liftBaseChange ℝ Λ.subtype.toIntLinearMap :
        ℝ ⊗[ℤ] Λ →ₗ[ℝ] V) ∧
      ∃ e : M ≃+ Dual ℤ Λ, ∀ φ z, (e φ z : ℝ) = (φ : Dual ℝ V) z := by
  classical
  let ι := Module.Free.ChooseBasisIndex ℤ M
  let b : Basis ι ℤ M := Module.Free.chooseBasis ℤ M
  obtain ⟨hli, hsp⟩ := hbasis b
  let B : Basis ι ℝ (Dual ℝ V) := Basis.mk hli hsp.ge
  let c : Basis ι ℝ V := B.dualBasis.map (Module.evalEquiv ℝ V).symm
  have hc : ∀ i j, (b i : Dual ℝ V) (c j) = if i = j then 1 else 0 := by
    intro i j
    have h1 : (b i : Dual ℝ V) (c j) = B.dualBasis j (B i) := by
      have : Module.evalEquiv ℝ V (c j) = B.dualBasis j := by simp [c]
      rw [← this, Module.evalEquiv_apply, Module.Dual.eval_apply, Basis.mk_apply]
    rw [h1, Basis.dualBasis_apply_self]
  have hrepr : ∀ (φ : M) j, (φ : Dual ℝ V) (c j) = b.repr φ j := by
    intro φ j
    conv_lhs => rw [← b.sum_repr φ]
    rw [AddSubgroup.val_finset_sum, LinearMap.sum_apply, Finset.sum_eq_single j]
    · simp [hc]
    · intro i _ hij
      simp [hc, hij]
    · simp
  have hcΛ : ∀ j, c j ∈ Λ := fun j => (hΛ _).2 fun φ hφ => ⟨b.repr ⟨φ, hφ⟩ j, hrepr ⟨φ, hφ⟩ j⟩
  let cΛ : ι → Λ := fun j => ⟨c j, hcΛ j⟩
  have hliΛ : LinearIndependent ℤ cΛ := by
    have : LinearIndependent ℤ (Λ.subtype.toIntLinearMap ∘ cΛ) :=
      c.linearIndependent.restrict_scalars' ℤ
    exact this.of_comp
  have hspΛ : ⊤ ≤ Submodule.span ℤ (Set.range cΛ) := by
    rintro z -
    have hcrepr : ∀ j, c.repr z j = (b j : Dual ℝ V) z := fun j => by
      simp [c, Basis.map_repr, Basis.dualBasis_repr, B]
    choose n hn using fun j => (hΛ z).1 z.2 _ (b j).2
    have hz : z = ∑ j, n j • cΛ j := by
      apply Subtype.ext
      simp only [AddSubgroup.val_finset_sum, AddSubgroup.coe_zsmul, cΛ]
      conv_lhs => rw [← c.sum_repr z]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hcrepr, hn j, Int.cast_smul_eq_zsmul]
    rw [hz]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let bΛ : Basis ι ℤ Λ := Basis.mk hliΛ hspΛ
  have hbΛ : ∀ j, (bΛ j : V) = c j := fun j => by simp [bΛ, cΛ]
  refine ⟨Module.Free.of_basis bΛ, Module.Finite.of_basis bΛ, ?_, ?_⟩
  · let T : Basis ι ℝ (ℝ ⊗[ℤ] Λ) := Algebra.TensorProduct.basis ℝ bΛ
    have : (LinearMap.liftBaseChange ℝ Λ.subtype.toIntLinearMap : ℝ ⊗[ℤ] Λ →ₗ[ℝ] V) =
        (T.equiv c (Equiv.refl ι)).toLinearMap := by
      refine T.ext fun i => ?_
      rw [LinearEquiv.coe_coe, Basis.equiv_apply, Equiv.refl_apply,
        Algebra.TensorProduct.basis_apply, LinearMap.liftBaseChange_tmul, one_smul]
      exact hbΛ i
    rw [this]
    exact (T.equiv c (Equiv.refl ι)).bijective
  · let e : M ≃ₗ[ℤ] Dual ℤ Λ :=
      (b.repr.trans (Finsupp.linearEquivFunOnFinite ℤ ℤ ι)).trans (bΛ.constr ℤ)
    refine ⟨e.toAddEquiv, fun φ z => ?_⟩
    have : (Int.castAddHom ℝ).toIntLinearMap ∘ₗ e φ =
        ((φ : Dual ℝ V).restrictScalars ℤ) ∘ₗ Λ.subtype.toIntLinearMap := by
      refine bΛ.ext fun j => ?_
      simp [e, Basis.constr_basis, hbΛ, hrepr]
    exact LinearMap.congr_fun this z

end Lattice

/-- The `ℝ`-linear extension of a form on `Λ ⊆ W` agreeing with `ψ` is `ψ` after `ℝ ⊗_ℤ Λ → W`. -/
private theorem liftBaseChange_apply_eq_apply {W : Type*} [AddCommGroup W] [Module ℝ W]
    (Λ : AddSubgroup W) {g : Λ →ₗ[ℤ] ℝ} {ψ : Dual ℝ W} (hg : ∀ z : Λ, g z = ψ z)
    (w : ℝ ⊗[ℤ] Λ) :
    LinearMap.liftBaseChange ℝ g w = ψ (LinearMap.liftBaseChange ℝ Λ.subtype.toIntLinearMap w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul r z => simp [hg]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- The preimage of a pointed cone with trivial lineality space under an injective linear map
meets its negative only in `0`. -/
private theorem comap_inter_neg_eq_singleton_zero {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] {f : E →ₗ[ℝ] F} (hf : Function.Injective f)
    {C : PointedCone ℝ F} (hC : C.lineal = ⊥) :
    ((C.comap f : Set E) ∩ -(C.comap f : Set E)) = {0} := by
  ext w
  simp only [Set.mem_inter_iff, Set.mem_neg, SetLike.mem_coe, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have hl : f w ∈ C.lineal := PointedCone.mem_lineal.2 ⟨h1, by simpa using h2⟩
    rw [hC] at hl
    exact hf (by rw [(Submodule.mem_bot _).1 hl, map_zero])
  · rintro rfl
    exact ⟨zero_mem _, by simp⟩

/-- A real number equal to `u / v` with `0 < v ≤ a(n + 1)` lies in `(1/(a(n+1))!) ℤ`. -/
private theorem exists_int_eq_div_factorial {a u v : ℤ} {n : ℕ} {t : ℝ} (ha : 0 < a) (hv : 0 < v)
    (hva : v ≤ a * (n + 1)) (htuv : t = u / v) :
    ∃ m : ℤ, t = m / ((a.toNat * (n + 1)).factorial : ℤ) := by
  have hv' : ((v.toNat : ℕ) : ℤ) = v := Int.toNat_of_nonneg hv.le
  have ha' : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg ha.le
  have hvN : v.toNat ∣ (a.toNat * (n + 1)).factorial := Nat.dvd_factorial (by omega) (by
    zify
    rw [hv', ha']
    exact hva)
  obtain ⟨q, hq⟩ := hvN
  have hfac : (((a.toNat * (n + 1)).factorial : ℕ) : ℤ) = v * q := by
    rw [hq]
    push_cast
    rw [hv']
  have hq0 : (q : ℝ) ≠ 0 := by
    have h0 := Nat.factorial_pos (a.toNat * (n + 1))
    rw [hq] at h0
    exact_mod_cast (Nat.pos_of_mul_pos_left h0).ne'
  refine ⟨u * q, ?_⟩
  rw [htuv, hfac]
  push_cast
  rw [mul_div_mul_right _ _ hq0]

section Curves

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- A closed immersion with reduced source has kernel the vanishing ideal of its image. -/
private theorem ker_eq_vanishingIdeal_support {A B : Scheme.{u}} (g : A ⟶ B)
    [IsClosedImmersion g] [IsReduced A] :
    g.ker = Scheme.IdealSheafData.vanishingIdeal g.ker.support := by
  have hg : IsIso g.toImage := by
    apply IsClosedImmersion.isIso_of_ker_eq g g.imageι g.toImage <;> simp [Scheme.Hom.imageι]
  let e : A ≅ g.ker.subscheme := asIso g.toImage
  have : IsReduced g.ker.subscheme := isReduced_of_isOpenImmersion e.inv
  exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme g.ker g.ker.support rfl

/-- On a proper `k`-scheme, an integral closed subscheme `i : C ⟶ X` of dimension one is
isomorphic over `X` to the proper curve with the generic point of `i(C)`, so invertible sheaves
have the same degree on both. -/
private theorem exists_properCurve_degreeOn_eq [IsProper sX] {C : Scheme.{u}} (i : C ⟶ X)
    [IsClosedImmersion i] [IsIntegral C] [IsProper (i ≫ sX)] (hC : topologicalKrullDim C = 1) :
    ∃ Γ : ProperCurve sX, ∀ (L : X.Modules)
      [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
      degreeOn k sX i hC.le L = Γ.degree k L := by
  set x : X := i (genericPoint C) with hx
  have hrange : Set.range i = closure ({x} : Set X) := by
    rw [← Set.image_univ, ← (genericPoint_spec C).def, ← i.isClosedEmbedding.closure_image_eq,
      Set.image_singleton]
  have hsupp : i.ker.support = TopologicalSpace.Closeds.closure ({x} : Set X) := by
    apply TopologicalSpace.Closeds.ext
    rw [Scheme.Hom.support_ker, TopologicalSpace.Closeds.coe_closure, hrange, closure_closure]
  have hker : i.ker = (curveSubschemeAtι x).ker := by
    rw [ker_eq_vanishingIdeal_support i, hsupp, Scheme.IdealSheafData.ker_subschemeι]
  haveI := IsClosedImmersion.isIso_lift (curveSubschemeAtι x) i hker.symm
  let e : C ≅ curveSubschemeAt x :=
    asIso (IsClosedImmersion.lift (curveSubschemeAtι x) i hker.symm.le)
  have he : e.hom ≫ curveSubschemeAtι x = i := IsClosedImmersion.lift_fac _ _ _
  have hdimx : topologicalKrullDim (curveSubschemeAt x) = 1 := by
    rw [← hC]
    exact (IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph).symm
  refine ⟨⟨x, isProperCurve_of_isProper sX hdimx⟩, fun L _ => ?_⟩
  exact MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k sX i _ hC.le hdimx.le e he L

variable [IsProper sX] [IsLocallyNoetherian X] [IsNormal X]

/-- The intersection numbers of `ℚ`-Cartier `ℚ`-divisors with an integral closed curve are those
with a proper curve. -/
private theorem exists_properCurve_intersectionNumber_eq {C : Scheme.{u}} (i : C ⟶ X)
    [IsClosedImmersion i] [IsIntegral C] [IsProper (i ≫ sX)] (hC : topologicalKrullDim C = 1) :
    ∃ Γ : ProperCurve sX, ∀ (D : QDivisor X) (hD : D.IsQCartier),
      D.intersectionNumber k sX i hC.le hD = D.intersectionNumber k sX Γ.ι Γ.dim_le hD := by
  obtain ⟨Γ, hΓ⟩ := exists_properCurve_degreeOn_eq sX i hC
  exact ⟨Γ, fun D hD => by
    simp only [QDivisor.intersectionNumber, Divisor.degreeOn, hΓ]
    rfl⟩

/-- `H + tK` is nef if and only if `(H · Γ) + t (K · Γ) ≥ 0` for every proper curve `Γ`. -/
private theorem isNefCombination_iff_forall_properCurve {H K : QDivisor X} (hH : H.IsQCartier)
    (hK : K.IsQCartier) (t : ℝ) :
    QDivisor.IsNefCombination k sX H K t ↔ ∀ Γ : ProperCurve sX,
      0 ≤ (H.intersectionNumber k sX Γ.ι Γ.dim_le hH : ℝ) +
        t * (K.intersectionNumber k sX Γ.ι Γ.dim_le hK) := by
  rw [MMP.Positivity.isNefCombination_iff hH hK]
  refine ⟨fun h Γ => h Γ.scheme Γ.ι Γ.dim_eq, fun h C i _ _ _ hC => ?_⟩
  obtain ⟨Γ, hΓ⟩ := exists_properCurve_intersectionNumber_eq sX i hC
  rw [hΓ H hH, hΓ K hK]
  exact h Γ

/-- A `ℚ`-Cartier `ℚ`-divisor which is not nef is negative on some proper curve. -/
private theorem exists_properCurve_intersectionNumber_neg {D : QDivisor X} (hD : D.IsQCartier)
    (h : ¬ D.IsNef k sX) : ∃ Γ : ProperCurve sX, D.intersectionNumber k sX Γ.ι Γ.dim_le hD < 0 := by
  rw [QDivisor.isNef_iff D hD] at h
  push Not at h
  obtain ⟨C, i, _, _, _, hC, hneg⟩ := h
  obtain ⟨Γ, hΓ⟩ := exists_properCurve_intersectionNumber_eq sX i hC
  exact ⟨Γ, hΓ D hD ▸ hneg⟩

end Curves

section NumericalDivisors

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX]

/-- On an integral, locally Noetherian, normal, quasi-compact scheme every invertible module is
`𝒪(D)` for a Cartier divisor `D`. -/
private theorem exists_isCartier_divisorialSheaf_iso (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    ∃ D : Divisor X, D.IsCartier ∧ Nonempty (D.divisorialSheaf ≅ L) := by
  have := Stacks.SheafOfModules.isInvertible_of_tensorInvertible (X := X.toRingedSpace) L
  have : ∀ z : X.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace z) :=
    X.isLocalRing
  choose W hW a ha using fun y : X =>
    Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible (X := X.toRingedSpace) L y
  obtain ⟨y₀⟩ : Nonempty X := inferInstance
  let F : MMP.Mori.LocalFrame L :=
    { W := W, mem := hW, a := a, isLocalGenerator := fun y V hV => ha y V hV, base := y₀ }
  exact ⟨F.divisor, fun y => ⟨F.W y, F.mem y, _, F.isLocalEquation_divisor y⟩,
    ⟨(@asIso _ _ _ _ F.toDivisorialSheaf F.isIso_toDivisorialSheaf).symm⟩⟩

/-- Every form in `Num(X)` is the degree form of a Cartier divisor. -/
private theorem exists_isCartier_of_mem_numericalDivisorGroup {φ}
    (hφ : φ ∈ numericalDivisorGroup sX) :
    ∃ (D : Divisor X) (hD : D.IsCartier), ∀ Γ : ProperCurve sX,
      φ (OneCycle.numericalClass sX (Γ.cycle ℝ)) = D.degreeOn k sX Γ.ι Γ.dim_le hD := by
  induction hφ using AddSubgroup.closure_induction with
  | mem φ h =>
    obtain ⟨L, hL, rfl⟩ := h
    obtain ⟨D, hD, ⟨e⟩⟩ := exists_isCartier_divisorialSheaf_iso L
    refine ⟨D, hD, fun Γ => ?_⟩
    haveI := hD.isInvertibleModule_divisorialSheaf
    rw [NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle, ProperCurve.degree,
      ← degreeOn_eq_of_iso k sX Γ.ι Γ.dim_le e]
    rfl
  | zero =>
    exact ⟨0, Divisor.isCartier_zero, fun Γ => by
      rw [Divisor.degreeOn_zero']
      simp⟩
  | add φ ψ _ _ hφ hψ =>
    obtain ⟨D, hD, h⟩ := hφ
    obtain ⟨D', hD', h'⟩ := hψ
    exact ⟨D + D', hD.add hD', fun Γ => by
      rw [Divisor.degreeOn_add, LinearMap.add_apply, h, h']
      push_cast
      rfl⟩
  | neg φ _ hφ =>
    obtain ⟨D, hD, h⟩ := hφ
    exact ⟨-D, hD.neg, fun Γ => by
      rw [Divisor.degreeOn_neg', LinearMap.neg_apply, h]
      push_cast
      rfl⟩

end NumericalDivisors

section Cone

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- The lattice `N₁(X)_ℤ` consists of the classes on which every form of `Num(X)` is integral. -/
private theorem mem_numericalCurveLattice_iff (z : NumericalCurveClasses sX) :
    z ∈ numericalCurveLattice sX ↔ ∀ φ ∈ numericalDivisorGroup sX, ∃ n : ℤ, φ z = n := by
  refine ⟨fun hz φ hφ => ?_, fun h L _ => h _ (AddSubgroup.subset_closure ⟨L, inferInstance, rfl⟩)⟩
  induction hφ using AddSubgroup.closure_induction with
  | mem φ h =>
    obtain ⟨L, hL, rfl⟩ := h
    exact @hz L hL
  | zero => exact ⟨0, by simp⟩
  | add φ ψ _ _ hφ hψ =>
    obtain ⟨n, hn⟩ := hφ
    obtain ⟨m, hm⟩ := hψ
    exact ⟨n + m, by simp [hn, hm]⟩
  | neg φ _ hφ =>
    obtain ⟨n, hn⟩ := hφ
    exact ⟨-n, by simp [hn]⟩

/-- A continuous linear form nonnegative on the classes of proper curves is nonnegative on
`NE̅(X)`. -/
private theorem nonneg_of_mem_closedConeOfCurves {ψ : Dual ℝ (NumericalCurveClasses sX)}
    (hψ : Continuous ψ) (h : ∀ Γ : ProperCurve sX, 0 ≤ ψ (OneCycle.numericalClass sX (Γ.cycle ℝ)))
    {z : NumericalCurveClasses sX} (hz : z ∈ closedConeOfCurves sX) : 0 ≤ ψ z := by
  have hsub : (coneOfCurves sX : Set (NumericalCurveClasses sX)) ⊆ {z | 0 ≤ ψ z} := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨Γ, rfl⟩ := hx
      exact h Γ
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Set.mem_setOf_eq, map_add] at hx hy ⊢
      exact add_nonneg hx hy
    | smul c x _ hx =>
      change 0 ≤ ψ ((c : ℝ) • x)
      rw [map_smul, smul_eq_mul]
      exact mul_nonneg c.2 hx
  rw [← SetLike.mem_coe, coe_closedConeOfCurves] at hz
  exact closure_minimal hsub (isClosed_le continuous_const hψ) hz

/-- A real-linear map from a finite-dimensional real space with its module topology to `N₁(X)`
is continuous for the numerical topology. -/
private theorem continuous_of_linearMap {W : Type*} [AddCommGroup W] [Module ℝ W]
    [TopologicalSpace W] [IsModuleTopology ℝ W] (g : W →ₗ[ℝ] NumericalCurveClasses sX) :
    Continuous g :=
  continuous_iInf_rng.2 fun L => continuous_iInf_rng.2 fun h => continuous_induced_rng.2 <| by
    haveI := h
    exact IsModuleTopology.continuous_of_linearMap (NumericalCurveClasses.degree sX L ∘ₗ g)

/-- The preimage of `NE̅(X)` under a real-linear map is closed for the module topology. -/
private theorem isClosed_preimage_closedConeOfCurves {W : Type*} [AddCommGroup W] [Module ℝ W]
    (g : W →ₗ[ℝ] NumericalCurveClasses sX) :
    @IsClosed W (moduleTopology ℝ W) (g ⁻¹' (closedConeOfCurves sX : Set _)) := by
  letI := moduleTopology ℝ W
  haveI : IsModuleTopology ℝ W := ⟨rfl⟩
  have hcl : IsClosed (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) := by
    rw [coe_closedConeOfCurves]
    exact isClosed_closure
  exact hcl.preimage (continuous_of_linearMap sX g)

private theorem intCast_floor_apply (φ : numericalDivisorGroup sX)
    (z : numericalCurveLattice sX) :
    ((⌊(φ : Dual ℝ (NumericalCurveClasses sX)) (z : NumericalCurveClasses sX)⌋ : ℤ) : ℝ) =
      (φ : Dual ℝ (NumericalCurveClasses sX)) (z : NumericalCurveClasses sX) := by
  obtain ⟨n, hn⟩ := (mem_numericalCurveLattice_iff sX z).1 z.2 φ φ.2
  rw [hn, Int.floor_intCast]

end Cone

end MMP.FourfoldProofs.Km3bConeHypothesesFromRationalityProof

namespace MMP.Mori

open CategoryTheory AlgebraicGeometry Module MMP.FourfoldProofs.Km3bConeHypothesesFromRationalityProof

section RestrictLattice

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- Restriction `Num(X) → Hom(N₁(X)_ℤ, ℤ)`: a form of `Num(X)` is integral on `N₁(X)_ℤ`, and
`restrictLattice sX φ` is its restriction there, read as an integral form. -/
noncomputable def numericalDivisorGroup.restrictLattice :
    numericalDivisorGroup sX →+ Dual ℤ (numericalCurveLattice sX) where
  toFun φ := AddMonoidHom.toIntLinearMap
    { toFun := fun z => ⌊(φ : Dual ℝ (NumericalCurveClasses sX)) (z : NumericalCurveClasses sX)⌋
      map_zero' := by simp
      map_add' := fun z w => Int.cast_injective (α := ℝ) <| by
        rw [Int.cast_add, intCast_floor_apply, intCast_floor_apply, intCast_floor_apply,
          AddSubgroup.coe_add, map_add] }
  map_zero' := by
    ext z
    simp
  map_add' φ ψ := by
    ext z
    refine Int.cast_injective (α := ℝ) ?_
    simp only [AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      LinearMap.add_apply]
    rw [Int.cast_add, intCast_floor_apply, intCast_floor_apply, intCast_floor_apply,
      AddSubgroup.coe_add, LinearMap.add_apply]

/-- The restriction `restrictLattice sX φ` takes the values of `φ` on `N₁(X)_ℤ`. -/
@[simp]
theorem numericalDivisorGroup.intCast_restrictLattice_apply (φ : numericalDivisorGroup sX)
    (z : numericalCurveLattice sX) :
    ((numericalDivisorGroup.restrictLattice sX φ z : ℤ) : ℝ) =
      (φ : Dual ℝ (NumericalCurveClasses sX)) (z : NumericalCurveClasses sX) :=
  intCast_floor_apply sX φ z

end RestrictLattice

/-- On a proper variety over an algebraically closed field of characteristic zero, restriction
`Num(X) → Hom(N₁(X)_ℤ, ℤ)` is bijective. -/
theorem numericalDivisorGroup.bijective_restrictLattice {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsProperVariety k sX] :
    Function.Bijective (numericalDivisorGroup.restrictLattice sX) := by
  haveI := NumericalCurveClasses.finiteDimensional_of_isProperVariety sX
  obtain ⟨_, _, -, hbasis⟩ := numericalDivisorGroup_free_finrank_and_basis sX
  obtain ⟨-, -, -, e, he⟩ := lattice_facts (numericalDivisorGroup sX) hbasis
    (numericalCurveLattice sX) (mem_numericalCurveLattice_iff sX)
  have : ⇑(numericalDivisorGroup.restrictLattice sX) = e := by
    funext φ
    ext z
    exact Int.cast_injective (α := ℝ) (by rw [intCast_restrictLattice_apply, he])
  rw [this]
  exact e.bijective

/-- The identification `Num(X) ≃ Hom(N₁(X)_ℤ, ℤ)` by restriction, on a proper variety over an
algebraically closed field of characteristic zero. -/
noncomputable def numericalDivisorGroupEquivDual {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsProperVariety k sX] :
    numericalDivisorGroup sX ≃+ Dual ℤ (numericalCurveLattice sX) :=
  AddEquiv.ofBijective (numericalDivisorGroup.restrictLattice sX)
    (numericalDivisorGroup.bijective_restrictLattice sX)

/-- `numericalDivisorGroupEquivDual sX φ` takes the values of `φ` on `N₁(X)_ℤ`. -/
@[simp]
theorem intCast_numericalDivisorGroupEquivDual_apply {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsProperVariety k sX]
    (φ : numericalDivisorGroup sX) (z : numericalCurveLattice sX) :
    ((numericalDivisorGroupEquivDual sX φ z : ℤ) : ℝ) =
      (φ : Dual ℝ (NumericalCurveClasses sX)) (z : NumericalCurveClasses sX) :=
  numericalDivisorGroup.intCast_restrictLattice_apply sX φ z

end MMP.Mori

namespace MMP.FourfoldProofs.Km3bConeHypothesesFromRationalityProof

open CategoryTheory AlgebraicGeometry TensorProduct Module MMP.Mori

/-- The curve form of a `ℚ`-Cartier `ℚ`-divisor is `1/m` times a continuous form of `Num(X)`,
`m` the Cartier index. -/
private theorem exists_curveForm_eq_inv_smul {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [AlgebraicGeometry.IsProjectiveVariety k sX]
    {D : QDivisor X} (hq : D.IsQCartier) :
    ∃ ψ ∈ numericalDivisorGroup sX, Continuous ψ ∧
      MMP.Fourfold.QDivisor.curveForm sX D hq = ((D.cartierIndex hq : ℕ) : ℝ)⁻¹ • ψ := by
  set E : Divisor X := (D.cartierIndexSMul hq : Divisor X)
  have hE : E.IsCartier := Divisor.mem_cartierSubgroup.mp (D.cartierIndexSMul hq).2
  haveI := hE.isInvertibleModule_divisorialSheaf
  refine ⟨NumericalCurveClasses.degree sX E.divisorialSheaf,
    AddSubgroup.subset_closure ⟨_, inferInstance, rfl⟩,
    NumericalCurveClasses.continuous_degree sX _,
    MMP.ProgramBaseChange.linearMap_ext_numericalClass_cycle sX fun Γ => ?_⟩
  rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle, LinearMap.smul_apply,
    NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle,
    QDivisor.intersectionNumber_eq_of_toQDivisor_eq k sX Γ.ι Γ.dim_le _ hq E hE
      (QDivisor.toQDivisor_cartierIndexSMul _ hq)]
  push_cast
  rw [div_eq_inv_mul, smul_eq_mul]
  rfl

/-- A Cartier divisor whose degree form is positive on `NE̅(X) \ 0` is nef and big. -/
private theorem isNef_and_isBig_of_forall_closedConeOfCurves_pos {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
    [AlgebraicGeometry.IsProjectiveVariety k sX] {D : Divisor X} (hD : D.IsCartier)
    [Stacks.Ample.IsInvertibleModule X D.divisorialSheaf]
    (hpos : ∀ z ∈ closedConeOfCurves sX, z ≠ 0 →
      0 < NumericalCurveClasses.degree sX D.divisorialSheaf z) :
    D.IsNef k sX ∧ D.IsBig k sX := by
  obtain ⟨E', ⟨iso⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf D.divisorialSheaf
  have hdeg : NumericalCurveClasses.degree sX (MMP.CartierDivisor.sheaf E') =
      NumericalCurveClasses.degree sX D.divisorialSheaf := by
    refine MMP.ProgramBaseChange.linearMap_ext_numericalClass_cycle sX fun Γ => ?_
    rw [NumericalCurveClasses.degree_numericalClass, NumericalCurveClasses.degree_numericalClass,
      OneCycle.degree_cycle, OneCycle.degree_cycle, ProperCurve.degree, ProperCurve.degree,
      degreeOn_eq_of_iso k sX Γ.ι Γ.dim_le iso]
  have hampE : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf E') :=
    (isAmple_cartierSheaf_iff_forall_closedConeOfCurves_pos sX E').2 fun z hz hz0 => by
      rw [NumericalCurveClasses.intersectionNumber_ofCartier, hdeg]
      exact hpos z hz hz0
  have hampD : D.IsAmple hD := (Stacks.RelativeVeryAmple.isAmple_congr _ _ iso).2 hampE
  have hqD : (Divisor.toQDivisor D).IsQCartier := QDivisor.isQCartier_toQDivisor hD
  have hall : ∀ m : ℕ, (Divisor.toQDivisor D).IsAmple ∧
      (Divisor.toQDivisor D).NumericallyEquivalent k sX
        (Divisor.toQDivisor D + (m : ℚ)⁻¹ • 0) := fun m =>
    ⟨⟨1, one_pos, D, by simp, hD, hampD⟩, by
      rw [smul_zero, add_zero]
      exact ⟨hqD, hqD, fun _ _ _ _ _ _ => rfl⟩⟩
  exact Divisor.isNef_and_isBig_of_numericallyEquivalent_isAmple_add_smul sX D hD 0 le_rfl
    QDivisor.isQCartier_zero (fun _ => Divisor.toQDivisor D)
    (Set.infinite_univ.mono fun m _ => hall m)

/-- For a klt pair `(X, Δ)` as in the rationality theorem, the `(K_X + Δ)`-threshold on `NE̅(X)`
of a form of `Num(X)` positive on `NE̅(X) \ 0` lies in `(1/(a(n+1))!) ℤ`. -/
private theorem exists_int_eq_div_factorial_of_isConeThreshold {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
    [AlgebraicGeometry.IsProjectiveVariety k sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hklt : IsKltPair sX n K Δ) (hΔ : Δ.IsEffective)
    (hnef : ¬ QDivisor.IsNef k sX (Divisor.toQDivisor K + Δ)) {a : ℤ} (ha : 0 < a)
    (hCart : QDivisor.IsCartierDivisor (a • (Divisor.toQDivisor K + Δ)))
    (hκc : Continuous (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2))
    {φ : Dual ℝ (NumericalCurveClasses sX)} (hφ : φ ∈ numericalDivisorGroup sX)
    (hpos : ∀ z ∈ closedConeOfCurves sX, z ≠ 0 → 0 < φ z) {t : ℝ}
    (ht : IsConeThreshold (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) φ
      (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2) t) :
    ∃ m : ℤ, t = m / ((a.toNat * (n + 1)).factorial : ℤ) := by
  have hq := hklt.1.2.2
  set κ := MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2
  obtain ⟨D, hD, hφD⟩ := exists_isCartier_of_mem_numericalDivisorGroup sX hφ
  haveI := hD.isInvertibleModule_divisorialSheaf
  have hφeq : φ = NumericalCurveClasses.degree sX D.divisorialSheaf :=
    MMP.ProgramBaseChange.linearMap_ext_numericalClass_cycle sX fun Γ => by
      rw [hφD, NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle]
      rfl
  have hnb := isNef_and_isBig_of_forall_closedConeOfCurves_pos hD (by rwa [hφeq] at hpos)
  have hqD : (Divisor.toQDivisor D).IsQCartier := QDivisor.isQCartier_toQDivisor hD
  have key : ∀ s : ℝ, (∀ z ∈ closedConeOfCurves sX, 0 ≤ φ z + s * κ z) ↔
      QDivisor.IsNefCombination k sX (Divisor.toQDivisor D) (Divisor.toQDivisor K + Δ) s := by
    intro s
    rw [isNefCombination_iff_forall_properCurve sX hqD hq]
    have hval : ∀ Γ : ProperCurve sX,
        φ (OneCycle.numericalClass sX (Γ.cycle ℝ)) +
            s * κ (OneCycle.numericalClass sX (Γ.cycle ℝ)) =
          ((Divisor.toQDivisor D).intersectionNumber k sX Γ.ι Γ.dim_le hqD : ℝ) +
            s * ((Divisor.toQDivisor K + Δ).intersectionNumber k sX Γ.ι Γ.dim_le hq : ℝ) :=
      fun Γ => by
        rw [hφD, MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
          QDivisor.intersectionNumber_toQDivisor k sX Γ.ι Γ.dim_le D hD hqD]
        push_cast
        rfl
    refine ⟨fun h Γ => ?_, fun h z hz => ?_⟩
    · rw [← hval]
      exact h _ (coneOfCurves_le_closedConeOfCurves sX (numericalClass_cycle_mem_coneOfCurves sX Γ))
    · have hc : Continuous (φ + s • κ) := by
        rw [hφeq]
        exact (NumericalCurveClasses.continuous_degree sX _).add (continuous_const.mul hκc)
      simpa using nonneg_of_mem_closedConeOfCurves sX hc (fun Γ => by
        rw [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hval]
        exact h Γ) hz
  have hthr : QDivisor.IsNefThreshold k sX (Divisor.toQDivisor D)
      (Divisor.toQDivisor K + Δ) t :=
    ⟨(key t).1 ht.1, fun t' ht' h => ht.2 t' ht' ((key t').2 h)⟩
  have hRD : IsRationalityDatum sX n K Δ a D :=
    ⟨inferInstance, hklt, hΔ, hnef, ha, hCart, hD, hnb.1, hnb.2⟩
  obtain ⟨u, v, hv, hva, htuv⟩ := hRD.exists_den_le_of_isNefThreshold hthr
  exact exists_int_eq_div_factorial ha hv hva htuv

end MMP.FourfoldProofs.Km3bConeHypothesesFromRationalityProof

end

section

/-!
## The cone datum

Let `X` be a projective variety of dimension `n` over an algebraically closed field `k` of
characteristic zero, `(X, Δ)` a klt pair with `Δ` effective and `K_X + Δ` not nef, and `a > 0`
an integer with `a(K_X + Δ)` Cartier. The lattice `N₁(X)_ℤ ⊆ N₁(X)` of numerical classes on which
every invertible sheaf has integral degree is a free `ℤ`-module of finite rank, the canonical map
`ℝ ⊗_ℤ N₁(X)_ℤ → N₁(X)` is an isomorphism, and restriction to `N₁(X)_ℤ` identifies the group
`Num(X)` of the forms `z ↦ (L · z)` with `Hom(N₁(X)_ℤ, ℤ)`. Moreover
`(N₁(X)_ℤ, NE̅(X), K, (a(n + 1))!)`, with `K` the form `z ↦ ((K_X + Δ) · z)`, is a cone datum:
the threshold condition is the rationality theorem
`MMP.Mori.IsRationalityDatum.exists_den_le_of_isNefThreshold`, since `v ≤ a(n + 1)` divides
`(a(n + 1))!`.

### Implementation notes

The identification `N₁(X)_ℤ ⊗ ℝ = N₁(X)` is the bijectivity of the `ℝ`-linear extension
`LinearMap.liftBaseChange` of the inclusion `N₁(X)_ℤ ⊆ N₁(X)`, and the cone of the cone datum is
the preimage of `NE̅(X)` under it. The identification `Hom(N₁(X)_ℤ, ℤ) = Num(X)` is the
bijectivity of the restriction map `numericalDivisorGroup.restrictLattice`, from `Num(X)` to
`Hom(N₁(X)_ℤ, ℤ)`; the resulting equivalence is `numericalDivisorGroupEquivDual`. The form `K`
is the rational form `N₁(X)_ℤ → ℚ` whose real values are those of
`MMP.Fourfold.QDivisor.curveForm` of `K_X + Δ`.
The freeness and finiteness of `N₁(X)_ℤ` are asserted as instances, which the cone datum needs.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct Module
  MMP.FourfoldProofs.Km3bConeHypothesesFromRationalityProof

namespace MMP.Mori

/-- **The cone hypotheses from rationality** (Kollár–Mori 3.14). Let `X` be a projective variety
over an algebraically closed field `k` of characteristic zero, `(X, Δ)` a klt pair with canonical
divisor `K` of dimension `n`, `Δ` effective and `K + Δ` not nef, and `a > 0` an integer with
`a(K + Δ)` Cartier. Then `N₁(X)_ℤ` is a free `ℤ`-module of finite rank, the canonical map
`ℝ ⊗_ℤ N₁(X)_ℤ → N₁(X)` is bijective, restriction is an isomorphism
`Num(X) ≃ Hom(N₁(X)_ℤ, ℤ)`, and there is a cone datum on `N₁(X)_ℤ` whose cone is `NE̅(X)`, whose
form is `z ↦ ((K + Δ) · z)` and whose index is `(a(n + 1))!`. -/
@[mmp "lem_km3b_cone_hypotheses_from_rationality"]
public theorem exists_coneDatum_numericalCurveLattice_of_isKltPair {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
    [AlgebraicGeometry.IsProjectiveVariety k sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hklt : IsKltPair sX n K Δ) (hΔ : Δ.IsEffective)
    (hnef : ¬ QDivisor.IsNef k sX (Divisor.toQDivisor K + Δ)) {a : ℤ} (ha : 0 < a)
    (hCart : QDivisor.IsCartierDivisor (a • (Divisor.toQDivisor K + Δ))) :
    ∃ (_ : Module.Free ℤ (numericalCurveLattice sX))
      (_ : Module.Finite ℤ (numericalCurveLattice sX)),
      Function.Bijective (LinearMap.liftBaseChange ℝ
        (numericalCurveLattice sX).subtype.toIntLinearMap :
          ℝ ⊗[ℤ] numericalCurveLattice sX →ₗ[ℝ] NumericalCurveClasses sX) ∧
      Function.Bijective (numericalDivisorGroup.restrictLattice sX) ∧
      ∃ D : ConeDatum (numericalCurveLattice sX),
        (D.cone : Set (ℝ ⊗[ℤ] numericalCurveLattice sX)) =
          LinearMap.liftBaseChange ℝ (numericalCurveLattice sX).subtype.toIntLinearMap ⁻¹'
            (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) ∧
        (∀ z : numericalCurveLattice sX,
          ((D.form z : ℚ) : ℝ) =
            MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2 z) ∧
        D.index = ((a.toNat * (n + 1)).factorial : ℤ) := by
  classical
  haveI : IsProper sX := inferInstance
  haveI := NumericalCurveClasses.finiteDimensional_of_isProperVariety sX
  obtain ⟨_, _, -, hbasis⟩ := numericalDivisorGroup_free_finrank_and_basis sX
  set Λ := numericalCurveLattice sX
  obtain ⟨hΛfree, hΛfin, hbij, e, he⟩ := lattice_facts (numericalDivisorGroup sX) hbasis
    Λ (mem_numericalCurveLattice_iff sX)
  refine ⟨hΛfree, hΛfin, hbij, numericalDivisorGroup.bijective_restrictLattice sX, ?_⟩
  set f : ℝ ⊗[ℤ] Λ →ₗ[ℝ] NumericalCurveClasses sX :=
    LinearMap.liftBaseChange ℝ Λ.subtype.toIntLinearMap
  have hq := hklt.1.2.2
  obtain ⟨ψ, hψ, hψc, hκ⟩ := exists_curveForm_eq_inv_smul (sX := sX) hq
  set κ := MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hq
  set c := (Divisor.toQDivisor K + Δ).cartierIndex hq
  let Kf : Λ →ₗ[ℤ] ℚ := (c : ℚ)⁻¹ • ((Int.castAddHom ℚ).toIntLinearMap ∘ₗ e ⟨ψ, hψ⟩)
  have hKf : ∀ z : Λ, ((Kf z : ℚ) : ℝ) = κ z := by
    intro z
    simp [Kf, hκ, he]
  have hKfR : ∀ w, realOfRatForm Λ Kf w = κ (f w) :=
    liftBaseChange_apply_eq_apply Λ fun z => by simpa using hKf z
  have hκc : Continuous κ := by
    rw [hκ]
    exact continuous_const.mul hψc
  refine ⟨
    { cone := (closedConeOfCurves sX).comap f
      isClosed_cone := ?_
      inter_neg_eq := ?_
      form := Kf
      exists_form_neg := ?_
      index := ((a.toNat * (n + 1)).factorial : ℤ)
      index_pos := by exact_mod_cast Nat.factorial_pos _
      threshold_mem := ?_ }, rfl, hKf, rfl⟩
  · exact isClosed_preimage_closedConeOfCurves sX f
  · exact comap_inter_neg_eq_singleton_zero hbij.1 (lineal_closedConeOfCurves_eq_bot (sX := sX))
  · obtain ⟨Γ, hΓ⟩ := exists_properCurve_intersectionNumber_neg sX hq hnef
    obtain ⟨w, hw⟩ := hbij.2 (OneCycle.numericalClass sX (Γ.cycle ℝ))
    refine ⟨w, show f w ∈ closedConeOfCurves sX from hw ▸
      coneOfCurves_le_closedConeOfCurves sX (numericalClass_cycle_mem_coneOfCurves sX Γ), ?_⟩
    rw [hKfR, hw, MMP.ProgramBaseChange.curveForm_numericalClass_cycle]
    exact_mod_cast hΓ
  · intro H hpos t ht
    set φ : Dual ℝ (NumericalCurveClasses sX) :=
      ((e.symm H : numericalDivisorGroup sX) : Dual ℝ (NumericalCurveClasses sX))
    have hHR : ∀ w, realOfIntForm Λ H w = φ (f w) := liftBaseChange_apply_eq_apply Λ fun z => by
      have := he (e.symm H) z
      rwa [AddEquiv.apply_symm_apply] at this
    have hiff : ∀ s : ℝ, (∀ w ∈ ((closedConeOfCurves sX).comap f : Set (ℝ ⊗[ℤ] Λ)),
        0 ≤ realOfIntForm Λ H w + s * realOfRatForm Λ Kf w) ↔
        ∀ z ∈ closedConeOfCurves sX, 0 ≤ φ z + s * κ z := fun s => by
      simp only [hHR, hKfR]
      refine ⟨fun h z hz => ?_, fun h w hw => h _ hw⟩
      obtain ⟨w, rfl⟩ := hbij.2 z
      exact h w hz
    refine exists_int_eq_div_factorial_of_isConeThreshold hklt hΔ hnef ha hCart hκc (e.symm H).2
      (fun z hz hz0 => ?_) ⟨(hiff t).1 ht.1, fun t' ht' h => ht.2 t' ht' ((hiff t').2 h)⟩
    obtain ⟨w, rfl⟩ := hbij.2 z
    rw [← hHR]
    exact hpos w hz (by rintro rfl; exact hz0 (map_zero f))

end MMP.Mori

end
