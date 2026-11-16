module

public import MMP.AlgebraicGeometry.Curves.Maps.Tangent
public import MMP.AlgebraicGeometry.ProjectiveSpace.ZeroLocusFactorization
public import MMP.AlgebraicGeometry.Curves.Maps.CoefficientSpace
public import StacksFrontier.AlgebraicGeometry.VanishingSystemImmersion.Restriction

/-!
# Sections over the base change of a curve to a `k`-algebra, and families of curve maps

For a `k`-scheme `X`, a `k`-algebra `B` and the fibre product `Y = X ×ₖ Spec B` with projection
`p : Y ⟶ X`, the functions on the preimage `p⁻¹ V` of a quasi-compact quasi-separated open `V`
of `X` are `Γ(X, V) ⊗_k B` (flat base change, `B` being flat over the field `k`). In a frame
`σ` of an invertible sheaf `L` on `V`, a section `Σⱼ q^* cⱼ · p^* wⱼ` of `p^* L` is the image of
`Σⱼ (wⱼ / σ) ⊗ cⱼ` times `p^* σ`.

Chart evaluations `T_m ↦ τ_m / τ_i` of a tuple of sections of an invertible sheaf vanish on a
homogeneous polynomial as soon as they vanish in local frames.

For a chart cover of a curve map `f : C ⟶ U` and a family `Φ : C ×ₖ Spec A ⟶ U` over a local
Artinian `k`-algebra `A` which reduces to `f` over the closed point and is constant along the
marked points, the maps `Γ(W_s, 𝒪_U) → Γ(p⁻¹ U_s) ≅ Γ(U_s, 𝒪_C) ⊗_k A` form a point of the curve
map on the charts; when `Φ` is given by a tuple of coefficients, the local expressions of the
tuple are a unit multiple of the images of the chart coordinates.

## Main definitions

* `MMP.Fourfold.CurveMapSections.baseChangeEquiv`: the ring isomorphism
  `Γ(X, V) ⊗_k B ≃ Γ(Y, p⁻¹ V)`.
* `MMP.Fourfold.CurveMapSections.familyChartMap`: the map on charts of a family over `Spec A`.
* `MMP.Fourfold.CurveMapSections.familyCurvePoint`: the corresponding point on the charts.
* `MMP.Fourfold.CurveMapSections.pointEvalₐ`: the value at a `k`-point as a `k`-algebra map.

## Main results

* `MMP.Fourfold.CurveMapSections.baseChangeEquiv_tmul`: it sends `a ⊗ b` to `p^* a · q^* b`.
* `MMP.Fourfold.CurveMapSections.baseChangeEquiv_res`: it commutes with restriction.
* `MMP.Fourfold.CurveMapSections.resT_coordSection_eq_smul`: coordinate sections in a frame.
* `MMP.Fourfold.CurveMapSections.chartEval_eq_zero_of_local`,
  `MMP.Fourfold.CurveMapSections.generatesStalks_of_local`: chart evaluations and generation from
  local frames.
* `MMP.Fourfold.CurveMapSections.familyChartMap_res`,
  `MMP.Fourfold.CurveMapSections.familyChartMap_fix`: the family reduces to `f` over the closed
  point and along the marked points.
* `MMP.Fourfold.CurveMapSections.exists_frames_familyChartMap`: the frames of a family given by
  coefficients.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped TensorProduct

universe u

namespace MMP.Fourfold.CurveMapSections

open MMP.Fourfold MMP.Fourfold.CurveMapCharts

section BaseChange

variable {k : Type u} [Field k] (B : Type u) [CommRing B] [Algebra k B]

/-- The structure morphism `Spec B ⟶ Spec k` of a `k`-algebra. -/
abbrev specStructMap : Spec (.of B) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k B))

/-- The structure morphism `Spec B ⟶ Spec k` of a `k`-algebra is flat. -/
instance flat_specStructMap : Flat (specStructMap (k := k) B) :=
  Flat.SpecMap_iff.mpr (by
    change (algebraMap k B).Flat
    rw [RingHom.flat_algebraMap_iff]; infer_instance)

variable {B} {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) {p : Y ⟶ X} {q : Y ⟶ Spec (.of B)}
  (H : IsPullback p q sX (specStructMap (k := k) B))

include H in
/-- **Flat base change for the functions on an open**: the square of rings
`k → Γ(X, V)`, `k → B`, `Γ(X, V) → Γ(Y, p⁻¹ V)`, `B → Γ(Y, p⁻¹ V)` is a pushout, for `V`
quasi-compact and quasi-separated. -/
theorem isPushout_sections (V : X.Opens) (hV : IsCompact (V : Set X))
    (hV' : IsQuasiSeparated (V : Set X)) :
    letI := CurveMapCharts.sectionsAlgebra sX V
    IsPushout (CommRingCat.ofHom (algebraMap k Γ(X, V))) (CommRingCat.ofHom (algebraMap k B))
      (p.appLE V (p ⁻¹ᵁ V) le_rfl)
      ((Scheme.ΓSpecIso (.of B)).inv ≫ q.appLE ⊤ (p ⁻¹ᵁ V) le_top) := by
  letI := CurveMapCharts.sectionsAlgebra sX V
  have hUST : (⊤ : (Spec (.of B)).Opens) ≤ specStructMap (k := k) B ⁻¹ᵁ ⊤ := le_top
  have hUSX : V ≤ sX ⁻¹ᵁ ⊤ := le_top
  have hUY : p ⁻¹ᵁ V = p ⁻¹ᵁ V ⊓ q ⁻¹ᵁ ⊤ := by simp
  have h := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H hUST hUSX hUY
    (isAffineOpen_top _) (isAffineOpen_top _) hV hV'
  have h2 := (isIso_pushoutSection_iff H hUST hUSX hUY).1 h
  refine IsPushout.of_iso h2 (Scheme.ΓSpecIso (.of k)) (Iso.refl _) (Scheme.ΓSpecIso (.of B))
    (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id]
    change _ = _ ≫ Stacks.Cech.baseRingHom sX V
    rw [Stacks.Cech.baseRingHom_eq_appLE sX V hUSX]
    exact (Iso.hom_inv_id_assoc (Scheme.ΓSpecIso (.of k)) _).symm
  · rw [show (specStructMap (k := k) B).appLE ⊤ ⊤ hUST = (specStructMap (k := k) B).appTop from
      Scheme.Hom.appLE_preimage_self _ _]
    exact Scheme.ΓSpecIso_naturality _
  · simp
  · simp

/-- **Flat base change for the functions on an open**, as a ring isomorphism
`Γ(X, V) ⊗_k B ≃ Γ(Y, p⁻¹ V)`. -/
def baseChangeEquiv (V : X.Opens) (hV : IsCompact (V : Set X))
    (hV' : IsQuasiSeparated (V : Set X)) :
    letI := CurveMapCharts.sectionsAlgebra sX V
    Γ(X, V) ⊗[k] B ≃+* Γ(Y, p ⁻¹ᵁ V) :=
  letI := CurveMapCharts.sectionsAlgebra sX V
  (IsPushout.isoIsPushout _ _ (CommRingCat.isPushout_tensorProduct k Γ(X, V) B)
    (isPushout_sections sX H V hV hV')).commRingCatIsoToRingEquiv

/-- The base change isomorphism sends `a ⊗ b` to the product of the pullbacks of `a` along `p`
and of `b` along `q`. -/
theorem baseChangeEquiv_tmul (V : X.Opens) (hV : IsCompact (V : Set X))
    (hV' : IsQuasiSeparated (V : Set X)) (a : Γ(X, V)) (b : B) :
    letI := CurveMapCharts.sectionsAlgebra sX V
    baseChangeEquiv sX H V hV hV' (a ⊗ₜ[k] b) =
      p.appLE V (p ⁻¹ᵁ V) le_rfl a *
        q.appLE ⊤ (p ⁻¹ᵁ V) le_top ((Scheme.ΓSpecIso (.of B)).inv b) := by
  letI := CurveMapCharts.sectionsAlgebra sX V
  have e : a ⊗ₜ[k] b = Algebra.TensorProduct.includeLeftRingHom a *
      Algebra.TensorProduct.includeRight.toRingHom b := by
    simp
  rw [e, map_mul]
  congr 1
  · exact ConcreteCategory.congr_hom (IsPushout.inl_isoIsPushout_hom _ _
      (CommRingCat.isPushout_tensorProduct k Γ(X, V) B) (isPushout_sections sX H V hV hV')) a
  · exact ConcreteCategory.congr_hom (IsPushout.inr_isoIsPushout_hom _ _
      (CommRingCat.isPushout_tensorProduct k Γ(X, V) B) (isPushout_sections sX H V hV hV')) b

/-- **Flat base change commutes with restriction.** -/
theorem baseChangeEquiv_res {V V' : X.Opens} (h : V' ≤ V) (hV : IsCompact (V : Set X))
    (hV' : IsQuasiSeparated (V : Set X)) (hW : IsCompact (V' : Set X))
    (hW' : IsQuasiSeparated (V' : Set X))
    (z : letI := CurveMapCharts.sectionsAlgebra sX V; Γ(X, V) ⊗[k] B) :
    letI := CurveMapCharts.sectionsAlgebra sX V
    letI := CurveMapCharts.sectionsAlgebra sX V'
    baseChangeEquiv sX H V' hW hW'
        (Algebra.TensorProduct.map (resAlgHom sX h) (AlgHom.id k B) z) =
      Y.presheaf.map (homOfLE (Scheme.Hom.preimage_mono p h)).op
        (baseChangeEquiv sX H V hV hV' z) := by
  letI := CurveMapCharts.sectionsAlgebra sX V
  letI := CurveMapCharts.sectionsAlgebra sX V'
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [Algebra.TensorProduct.map_tmul, baseChangeEquiv_tmul, baseChangeEquiv_tmul, map_mul]
    congr 1
    · rw [resAlgHom_apply, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
    · rw [AlgHom.id_apply]
      exact (ConcreteCategory.congr_hom (Scheme.Hom.appLE_map q _ (homOfLE _).op) _).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **Pulling back along a map into the base change.** For `φ : T ⟶ Y`, the composite of
`Γ(X, V) ⊗_k B ≃ Γ(Y, p⁻¹ V)` with `φ^*` sends `a ⊗ b` to `(φ ≫ p)^* a · (φ ≫ q)^* b`. -/
theorem appLE_baseChangeEquiv_tmul {T : Scheme.{u}} (φ : T ⟶ Y) (V : X.Opens)
    (hV : IsCompact (V : Set X)) (hV' : IsQuasiSeparated (V : Set X)) {W : T.Opens}
    (h : W ≤ φ ⁻¹ᵁ (p ⁻¹ᵁ V)) (a : Γ(X, V)) (b : B) :
    letI := CurveMapCharts.sectionsAlgebra sX V
    φ.appLE (p ⁻¹ᵁ V) W h (baseChangeEquiv sX H V hV hV' (a ⊗ₜ[k] b)) =
      (φ ≫ p).appLE V W h a * (φ ≫ q).appLE ⊤ W le_top ((Scheme.ΓSpecIso (.of B)).inv b) := by
  letI := CurveMapCharts.sectionsAlgebra sX V
  rw [baseChangeEquiv_tmul, map_mul]
  congr 1
  · exact ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE φ p V _ W le_rfl h) a
  · exact ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE φ q ⊤ _ W le_top h) _

/-- **The coordinate sections in a frame over the base change of a chart.** On `p⁻¹ V`, the
section `Σⱼ q^* cⱼ · p^* wⱼ` of `p^* L` is the image of `Σⱼ (wⱼ / σ) ⊗ cⱼ` times `p^* σ`. -/
theorem resT_coordSection_eq_smul (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    {N : ℕ} (w : Fin N → Γ(L, ⊤)) (c : Fin N → B) (σ : Γ(L, ⊤)) {V : X.Opens}
    (hσ : V ≤ Stacks.ProjectiveFromSections.nvOpen L σ) (hV : IsCompact (V : Set X))
    (hV' : IsQuasiSeparated (V : Set X)) :
    letI := CurveMapCharts.sectionsAlgebra sX V
    letI := Stacks.InvertiblePullback.isInvertibleModule_pullback p L
    Stacks.ProjectiveFromSections.resT (p ⁻¹ᵁ V)
        (Stacks.LinearSystemScheme.coordSection p q L w
          (fun j => (Scheme.ΓSpecIso (.of B)).inv (c j))) =
      baseChangeEquiv sX H V hV hV'
          (∑ j, Stacks.ProjectiveFromSections.div σ hσ
            (Stacks.ProjectiveFromSections.resT V (w j)) ⊗ₜ[k] c j) •
        Stacks.ProjectiveFromSections.resT (p ⁻¹ᵁ V) (pullbackGlobalSections p L σ) := by
  letI := CurveMapCharts.sectionsAlgebra sX V
  letI := Stacks.InvertiblePullback.isInvertibleModule_pullback p L
  have hW : p ⁻¹ᵁ V ≤ Stacks.ProjectiveFromSections.nvOpen ((Scheme.Modules.pullback p).obj L)
      (pullbackGlobalSections p L σ) := by
    rw [Stacks.RatioPullback.nvOpen_pullbackGlobalSections]
    exact fun x hx => hσ hx
  unfold Stacks.LinearSystemScheme.coordSection
  rw [map_sum, Finset.sum_smul]
  simp only [Stacks.ProjectiveFromSections.resT, Stacks.ProjectiveFromSections.resM, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 := Stacks.ProjectiveFromSections.resM_smul (L := (Scheme.Modules.pullback p).obj L)
    (le_top : p ⁻¹ᵁ V ≤ ⊤) (q.appTop ((Scheme.ΓSpecIso (.of B)).inv (c j)))
    (pullbackGlobalSections p L (w j))
  simp only [Stacks.ProjectiveFromSections.resM] at h1
  rw [h1]
  have h2 := Stacks.ProjectiveFromSections.div_smul _ hW
    (Stacks.ProjectiveFromSections.resT (p ⁻¹ᵁ V) (pullbackGlobalSections p L (w j)))
  rw [Stacks.RatioPullback.div_pullbackGlobalSections p L σ (w j) hσ hW le_rfl] at h2
  simp only [Stacks.ProjectiveFromSections.resT, Stacks.ProjectiveFromSections.resM] at h2
  rw [← h2, smul_smul, baseChangeEquiv_tmul, mul_comm]
  congr 1

end BaseChange

section Homogeneous

/-- **A homogeneous polynomial of degree `d` scales by `c ^ d`.** -/
theorem eval₂_mul_of_isHomogeneous {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) {F : MvPolynomial σ R} {d : ℕ} (hF : F.IsHomogeneous d) (c : S)
    (x : σ → S) :
    MvPolynomial.eval₂ f (fun m => c * x m) F = c ^ d * MvPolynomial.eval₂ f x F := by
  classical
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  rw [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [MvPolynomial.eval₂_monomial, MvPolynomial.eval₂_monomial]
  have hd : ∑ i ∈ α.support, α i = d := by
    have := hF (MvPolynomial.mem_support_iff.1 hα)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

end Homogeneous

end MMP.Fourfold.CurveMapSections

namespace MMP.Fourfold.CurveMapSections

section ChartEval

open Stacks.ProjectiveFromSections

/-- The map on global sections of the inclusion of an open is restriction, through `topIso`. -/
theorem ι_appTop_eq_topIso_inv {Y : Scheme.{u}} (W : Y.Opens) (x : Γ(Y, ⊤)) :
    W.ι.appTop x = W.topIso.inv (resO (le_top : W ≤ ⊤) x) := by
  have h : (homOfLE (x := W.ι ''ᵁ ⊤) le_top).op =
      (homOfLE (le_top : W ≤ ⊤)).op ≫ (eqToHom W.ι_image_top).op :=
    Subsingleton.elim _ _
  have h2 := congrArg (fun g' => Y.presheaf.map g' x) h
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.ConcreteCategory.comp_apply] at h2
  exact h2

variable {k : Type u} [Field k] {Y : Scheme.{u}} {M : Y.Modules}
  [Stacks.Ample.IsInvertibleModule Y M] {n : ℕ} (τ : Fin (n + 1) → Γ(M, ⊤))
  (π : Y ⟶ Spec (.of k))

/-- **The chart evaluation, on the chart itself**: `T_m ↦ τ_m / τ_i`, with `k` acting through
`π`. -/
theorem topIso_hom_chartEval (i : Fin (n + 1)) (F : MvPolynomial (Fin (n + 1)) k) :
    (nvCover τ i).topIso.hom (chartEval τ π i F) =
      MvPolynomial.eval₂ (Stacks.Cech.baseRingHom π (nvCover τ i)).hom (ratio τ i) F := by
  have hι : ∀ c : k, (nvCover τ i).topIso.hom
      (Stacks.ProjectiveSpaceChartRatio.baseRingHom ((nvCover τ i).ι ≫ π) c) =
      (Stacks.Cech.baseRingHom π (nvCover τ i)).hom c := by
    intro c
    have hc : (nvCover τ i).ι.appTop.hom.comp (Stacks.ProjectiveSpaceChartRatio.baseRingHom π) =
        Stacks.ProjectiveSpaceChartRatio.baseRingHom ((nvCover τ i).ι ≫ π) := by
      rw [Stacks.ProjectiveSpaceChartRatio.baseRingHom,
        Stacks.ProjectiveSpaceChartRatio.baseRingHom, Scheme.Hom.comp_appTop]
      rfl
    rw [← hc, RingHom.comp_apply, ι_appTop_eq_topIso_inv, Iso.inv_hom_id_apply]
    rfl
  rw [chartEval, MvPolynomial.coe_eval₂Hom]
  have := MvPolynomial.eval₂_comp_left (nvCover τ i).topIso.hom.hom
    (Stacks.ProjectiveSpaceChartRatio.baseRingHom ((nvCover τ i).ι ≫ π)) (chartRatio τ i) F
  refine this.trans ?_
  congr 1
  · exact RingHom.ext hι
  · funext m
    exact Iso.inv_hom_id_apply _ _

omit [Stacks.Ample.IsInvertibleModule Y M] in
/-- **A unit multiple of a nonvanishing section does not vanish.** -/
theorem le_nvOpen_of_resT_eq_smul [Stacks.Ample.IsInvertibleModule Y M] {V : Y.Opens}
    {s t : Γ(M, ⊤)} (ht : V ≤ nvOpen M t) {a : Γ(Y, V)} (ha : IsUnit a)
    (h : resT V s = a • resT V t) : V ≤ nvOpen M s := by
  obtain ⟨a', ha'⟩ : ∃ a' : Γ(Y, V), a' * a = 1 := ⟨((ha.unit⁻¹ : Γ(Y, V)ˣ) : Γ(Y, V)), ha.val_inv_mul⟩
  have h2 : resT V t = a' • resT V s := by rw [h, smul_smul, ha', one_smul]
  have e1 := Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn_res M (le_top : V ≤ ⊤) t
  have e2 := Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn_res M (le_top : V ≤ ⊤) s
  rw [Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn_top] at e1 e2
  intro y hy
  have hyt : y ∈ Stacks.Ample.nonvanishingLocus M t := ht hy
  have h3 : y ∈ Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn M V (resT V t) := by
    change y ∈ Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn M V
      (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t)
    rw [e1]; exact ⟨hy, hyt⟩
  rw [h2, Stacks.AmpleThickeningAscent.nonvanishingLocusOn_smul] at h3
  have h4 := h3.2
  change y ∈ Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn M V
    (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s) at h4
  rw [e2] at h4
  exact h4.2

/-- **Generation from local frames**: if on each member of a cover some `τ_m` is a unit multiple
of a nonvanishing section, the `τ_m` generate. -/
theorem generatesStalks_of_local {ι : Type*} (V : ι → Y.Opens) (hV : ∀ y : Y, ∃ t, y ∈ V t)
    (σ : ι → Γ(M, ⊤)) (hσ : ∀ t, V t ≤ nvOpen M (σ t)) (u : ∀ t, Fin (n + 1) → Γ(Y, V t))
    (hu : ∀ t m, resT (V t) (τ m) = u t m • resT (V t) (σ t))
    (hunit : ∀ t, ∃ m, IsUnit (u t m)) : GeneratesStalks τ := by
  refine (Stacks.AmpleImmersionReduction.generatesStalks_iff_forall_exists_mem τ).2 fun y => ?_
  obtain ⟨t, ht⟩ := hV y
  obtain ⟨m, hm⟩ := hunit t
  exact ⟨m, le_nvOpen_of_resT_eq_smul (hσ t) hm (hu t m) ht⟩

/-- **Chart evaluations vanish when they vanish in local frames.** If on each member `V_t` of a
cover `τ_m = u_{t m} · σ_t` with `σ_t` nonvanishing, and the homogeneous `F` vanishes on the
`u_t`, every chart evaluation of `τ` kills `F`. -/
theorem chartEval_eq_zero_of_local {ι : Type*} (V : ι → Y.Opens) (hV : ∀ y : Y, ∃ t, y ∈ V t)
    (σ : ι → Γ(M, ⊤)) (hσ : ∀ t, V t ≤ nvOpen M (σ t)) (u : ∀ t, Fin (n + 1) → Γ(Y, V t))
    (hu : ∀ t m, resT (V t) (τ m) = u t m • resT (V t) (σ t))
    {d : ℕ} {F : MvPolynomial (Fin (n + 1)) k} (hF : F.IsHomogeneous d)
    (hF0 : ∀ t, MvPolynomial.eval₂ (Stacks.Cech.baseRingHom π (V t)).hom (u t) F = 0)
    (i : Fin (n + 1)) : chartEval τ π i F = 0 := by
  apply (ConcreteCategory.bijective_of_isIso (nvCover τ i).topIso.hom).1
  rw [map_zero, topIso_hom_chartEval]
  refine TopCat.Sheaf.eq_of_locally_eq' Y.sheaf (fun t => nvCover τ i ⊓ V t) (nvCover τ i)
    (fun t => homOfLE inf_le_left) ?_ _ _ ?_
  · intro y hy
    obtain ⟨t, ht⟩ := hV y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨t, hy, ht⟩
  · intro t
    change (Y.presheaf.map (homOfLE (inf_le_left : nvCover τ i ⊓ V t ≤ nvCover τ i)).op).hom _ =
      (Y.presheaf.map (homOfLE (inf_le_left : nvCover τ i ⊓ V t ≤ nvCover τ i)).op).hom 0
    rw [map_zero]
    have hWτ : nvCover τ i ⊓ V t ≤ nvOpen M (τ i) := inf_le_left
    have hWσ : nvCover τ i ⊓ V t ≤ nvOpen M (σ t) := inf_le_right.trans (hσ t)
    set w := div (τ i) hWτ (resT (nvCover τ i ⊓ V t) (σ t)) with hw
    set v : Fin (n + 1) → Γ(Y, nvCover τ i ⊓ V t) := fun m => resO inf_le_right (u t m) with hv
    have hres : ∀ m, resT (nvCover τ i ⊓ V t) (τ m) =
        v m • resT (nvCover τ i ⊓ V t) (σ t) := by
      intro m
      have := congrArg (resM (L := M) (inf_le_right : nvCover τ i ⊓ V t ≤ V t)) (hu t m)
      rwa [resM_resT, resM_smul, resM_resT] at this
    have hr : ∀ m, resO (inf_le_left : nvCover τ i ⊓ V t ≤ nvCover τ i) (ratio τ i m) =
        w * v m := by
      intro m
      refine eq_of_smul_eq_smul (τ i) hWτ ?_
      rw [resO_ratio_smul τ inf_le_left m, mul_comm, mul_smul, hw, div_smul, hres m]
    have hF1 : (Y.presheaf.map (homOfLE (inf_le_right : nvCover τ i ⊓ V t ≤ V t)).op).hom
        (MvPolynomial.eval₂ (Stacks.Cech.baseRingHom π (V t)).hom (u t) F) = 0 := by
      rw [hF0 t, map_zero]
    rw [MvPolynomial.eval₂_comp_left] at hF1
    rw [MvPolynomial.eval₂_comp_left]
    have hb1 : (Y.presheaf.map (homOfLE (inf_le_left : nvCover τ i ⊓ V t ≤ nvCover τ i)).op).hom.comp
        (Stacks.Cech.baseRingHom π (nvCover τ i)).hom =
        (Stacks.Cech.baseRingHom π (nvCover τ i ⊓ V t)).hom :=
      congrArg CommRingCat.Hom.hom (Stacks.Cech.baseRingHom_map π _)
    have hb2 : (Y.presheaf.map (homOfLE (inf_le_right : nvCover τ i ⊓ V t ≤ V t)).op).hom.comp
        (Stacks.Cech.baseRingHom π (V t)).hom =
        (Stacks.Cech.baseRingHom π (nvCover τ i ⊓ V t)).hom :=
      congrArg CommRingCat.Hom.hom (Stacks.Cech.baseRingHom_map π _)
    rw [hb1]
    rw [hb2] at hF1
    have e : (⇑(Y.presheaf.map (homOfLE (inf_le_left : nvCover τ i ⊓ V t ≤ nvCover τ i)).op).hom ∘
        ratio τ i) = fun m => w * v m := funext hr
    rw [e, eval₂_mul_of_isHomogeneous _ hF]
    have e2 : (⇑(Y.presheaf.map (homOfLE (inf_le_right : nvCover τ i ⊓ V t ≤ V t)).op).hom ∘
        u t) = v := rfl
    rw [e2] at hF1
    rw [hF1, mul_zero]

/-- **A chart evaluation that vanishes vanishes on every open of the chart**, as the polynomial
evaluated at the restricted ratios. -/
theorem eval₂_resO_ratio_eq_zero (i : Fin (n + 1)) {F : MvPolynomial (Fin (n + 1)) k}
    (h0 : chartEval τ π i F = 0) {W : Y.Opens} (hW : W ≤ nvCover τ i) :
    MvPolynomial.eval₂ (Stacks.Cech.baseRingHom π W).hom (fun m => resO hW (ratio τ i m)) F =
      0 := by
  have h1 := topIso_hom_chartEval τ π i F
  rw [h0, map_zero] at h1
  have h2 := congrArg (fun z => (Y.presheaf.map (homOfLE hW).op).hom z) h1
  simp only [map_zero] at h2
  rw [MvPolynomial.eval₂_comp_left] at h2
  rw [← congrArg CommRingCat.Hom.hom (Stacks.Cech.baseRingHom_map π (homOfLE hW).op)]
  exact h2.symm

end ChartEval

section PullbackFrames

open Stacks.ProjectiveFromSections

variable {Y X' X : Scheme.{u}} (φ : Y ⟶ X') (ψ : X' ⟶ X) (L : X.Modules)
  [Stacks.Ample.IsInvertibleModule X L]

/-- **Local expressions pull back along a composite of pullbacks.** For `s, σ` global sections of
`L` with `σ` nonvanishing on `V`, the pullback of `s` along `ψ` then `φ` is, on `W ⊆ (φ ≫ ψ)⁻¹ V`,
the pullback of `s / σ` times the pullback of `σ`. -/
theorem resT_pullback_pullback_eq_smul (s σ : Γ(L, ⊤)) {V : X.Opens} (hV : V ≤ nvOpen L σ)
    {W : Y.Opens} (hW : W ≤ (φ ≫ ψ) ⁻¹ᵁ V) :
    letI := Stacks.InvertiblePullback.isInvertibleModule_pullback ψ L
    resT W (pullbackGlobalSections φ ((Scheme.Modules.pullback ψ).obj L)
        (pullbackGlobalSections ψ L s)) =
      (φ ≫ ψ).appLE V W hW (div σ hV (resT V s)) •
        resT W (pullbackGlobalSections φ ((Scheme.Modules.pullback ψ).obj L)
          (pullbackGlobalSections ψ L σ)) := by
  letI := Stacks.InvertiblePullback.isInvertibleModule_pullback ψ L
  have hV' : ψ ⁻¹ᵁ V ≤ nvOpen ((Scheme.Modules.pullback ψ).obj L) (pullbackGlobalSections ψ L σ) := by
    rw [Stacks.RatioPullback.nvOpen_pullbackGlobalSections]
    exact fun x hx => hV hx
  have hW' : W ≤ nvOpen ((Scheme.Modules.pullback φ).obj ((Scheme.Modules.pullback ψ).obj L))
      (pullbackGlobalSections φ _ (pullbackGlobalSections ψ L σ)) := by
    rw [Stacks.RatioPullback.nvOpen_pullbackGlobalSections]
    exact fun x hx => hV' (hW hx)
  have e1 := Stacks.RatioPullback.div_pullbackGlobalSections ψ L σ s hV hV' le_rfl
  have e2 := Stacks.RatioPullback.div_pullbackGlobalSections φ _ (pullbackGlobalSections ψ L σ)
    (pullbackGlobalSections ψ L s) hV' hW' hW
  rw [← div_smul _ hW' (resT W _), e2, e1]
  congr 1
  exact ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE φ ψ V (ψ ⁻¹ᵁ V) W le_rfl hW) _

/-- Restriction of a finite sum of global sections. -/
theorem resT_sum {Y : Scheme.{u}} {M : Y.Modules} (W : Y.Opens) {ι : Type*} (s : Finset ι)
    (x : ι → Γ(M, ⊤)) : resT W (∑ j ∈ s, x j) = ∑ j ∈ s, resT W (x j) := by
  simp only [resT, resM, map_sum]

/-- Restriction of a multiple of a global section. -/
theorem resT_smul {Y : Scheme.{u}} {M : Y.Modules} (W : Y.Opens) (a : Γ(Y, ⊤)) (x : Γ(M, ⊤)) :
    resT W (a • x) = resO (le_top : W ≤ ⊤) a • resT W x :=
  resM_smul _ _ _

/-- **Isomorphisms of modules preserve nonvanishing opens.** -/
theorem nvOpen_iso_app {Y : Scheme.{u}} {M M' : Y.Modules} [Stacks.Ample.IsInvertibleModule Y M]
    [Stacks.Ample.IsInvertibleModule Y M'] (e : M ≅ M') (t : Γ(M, ⊤)) :
    nvOpen M' (e.hom.app ⊤ t) = nvOpen M t :=
  TopologicalSpace.Opens.ext (nonvanishingLocus_app_top_eq_of_iso e t)

/-- **Isomorphisms of modules preserve ratios.** -/
theorem div_iso_app {Y : Scheme.{u}} {M M' : Y.Modules} [Stacks.Ample.IsInvertibleModule Y M]
    [Stacks.Ample.IsInvertibleModule Y M'] (e : M ≅ M') (σ s : Γ(M, ⊤)) {V : Y.Opens}
    (hV : V ≤ nvOpen M σ) (hV' : V ≤ nvOpen M' (e.hom.app ⊤ σ)) :
    div (e.hom.app ⊤ σ) hV' (resT V (e.hom.app ⊤ s)) = div σ hV (resT V s) := by
  refine (eq_div _ hV' ?_).symm
  have hr : ∀ x : Γ(M, ⊤), resT V (e.hom.app ⊤ x) = e.hom.app V (resT V x) := fun x =>
    (moduleHom_app_map e.hom (homOfLE (le_top : V ≤ ⊤)) x).symm
  rw [hr, hr, ← Scheme.Modules.Hom.app_smul, div_smul]

end PullbackFrames

section PointEval

variable {k : Type u} [Field k] {X : Scheme.{u}} (P : Spec (.of k) ⟶ X)

/-- **A function with value zero at a `k`-point vanishes there**: its germ lies in the maximal
ideal of the stalk. -/
theorem mem_maximalIdeal_of_pointEval_eq_zero {V : X.Opens} (hV : ⊤ ≤ P ⁻¹ᵁ V)
    (pt : Spec (.of k)) (hP : P.base pt ∈ V) (x : Γ(X, V))
    (hx : CurveMapTangent.pointEval P hV x = 0) :
    X.presheaf.germ V _ hP x ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk _) := by
  by_contra hne
  have hu : IsUnit (X.presheaf.germ V _ hP x) := by
    simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hne
  have h1 := congrArg (fun φ => φ.hom x) (Scheme.Hom.germ_stalkMap P V pt hP)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h1
  have e1 : ((Spec (.of k)).presheaf.germ ⊤ pt trivial) (P.appLE V ⊤ hV x) =
      P.stalkMap pt (X.presheaf.germ V _ hP x) := by
    rw [h1]
    exact TopCat.Presheaf.germ_res_apply _ (homOfLE hV) pt trivial (P.app V x)
  have hx' : P.appLE V ⊤ hV x = 0 := by
    have := congrArg (Scheme.ΓSpecIso (.of k)).inv hx
    rw [map_zero] at this
    rw [← this, CurveMapTangent.pointEval_apply, Iso.hom_inv_id_apply]
  rw [hx', map_zero] at e1
  have := (hu.map (P.stalkMap pt).hom)
  rw [← e1] at this
  exact not_isUnit_zero this

end PointEval

end MMP.Fourfold.CurveMapSections

namespace MMP.Fourfold.CurveMapSections

/-! ### The points on the charts of a family of curve maps over an Artinian base -/

section FamilyCurvePoint

open MMP.Fourfold MMP.Fourfold.CurveMapCharts MMP.Fourfold.CurveChartDeformations
open Stacks.ProjectiveFromSections

variable {k : Type u} [Field k] {C U : Scheme.{u}} (sC : C ⟶ Spec (.of k))
  (sU : U ⟶ Spec (.of k)) {f : C ⟶ U} (hf : f ≫ sU = sC) {ι : Type u} [DecidableEq ι]
  (K : ChartCover f ι) [IsSeparated sC] [IsSeparated sU] [Smooth sU] [CompactSpace C]
  [QuasiSeparatedSpace C]

include sC in
/-- The intersections of the source charts are quasi-compact and quasi-separated. -/
theorem isCompact_inf_UC (s : Finset ι) : IsCompact ((s.inf K.UC : C.Opens) : Set C) ∧
    IsQuasiSeparated ((s.inf K.UC : C.Opens) : Set C) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨isCompact_univ, IsQuasiSeparated.of_quasiSeparatedSpace _⟩
  · exact ⟨(K.isAffineOpen_inf_UC sC hs).isCompact, (K.isAffineOpen_inf_UC sC hs).isQuasiSeparated⟩

variable {b : ℕ} (pts : Fin b → C)
  (A : ArtinLocalAlgebra k) {Y : Scheme.{u}} {p : Y ⟶ C} {q : Y ⟶ Spec (.of A.carrier)}
  (H : IsPullback p q sC (specStructMap (k := k) A.carrier)) (Φ : Y ⟶ U)
  (hΦ : Φ ≫ sU = p ≫ sC)
  (hle : ∀ s : Finset ι, p ⁻¹ᵁ s.inf K.UC ≤ Φ ⁻¹ᵁ s.inf K.WU)

/-- **The map on charts of a family `Φ : C ×ₖ Spec A ⟶ U`**:
`Γ(W_s, 𝒪_U) → Γ(p⁻¹ U_s) ≅ Γ(U_s, 𝒪_C) ⊗_k A`. -/
def familyChartMap (s : Finset ι) :
    (curveCharts sC sU K hf pts).S s →ₐ[k]
      (curveCharts sC sU K hf pts).O s ⊗[k]
        A.carrier where
  toRingHom := (baseChangeEquiv sC H _ (isCompact_inf_UC sC K s).1
    (isCompact_inf_UC sC K s).2).symm.toRingHom.comp (Φ.appLE _ _ (hle s)).hom
  commutes' c := by
    letI := CurveMapCharts.sectionsAlgebra sC (s.inf K.UC)
    apply (baseChangeEquiv sC H _ (isCompact_inf_UC sC K s).1
      (isCompact_inf_UC sC K s).2).injective
    change baseChangeEquiv sC H _ _ _ ((baseChangeEquiv sC H _ _ _).symm _) = _
    rw [RingEquiv.apply_symm_apply, Algebra.TensorProduct.algebraMap_apply]
    change Φ.appLE _ _ (hle s) (Stacks.Cech.baseRingHom sU (s.inf K.WU) c) =
      baseChangeEquiv sC H (s.inf K.UC) (isCompact_inf_UC sC K s).1 (isCompact_inf_UC sC K s).2
        ((Stacks.Cech.baseRingHom sC (s.inf K.UC) c) ⊗ₜ[k] (1 : A.carrier))
    rw [baseChangeEquiv_tmul, map_one, map_one, mul_one]
    have h1 := ConcreteCategory.congr_hom (CurveMapCharts.baseRingHom_comp_appLE (p ≫ sC) sU hΦ
      (hle s)) c
    have h2 := ConcreteCategory.congr_hom (CurveMapCharts.baseRingHom_comp_appLE (p ≫ sC) sC rfl
      (le_refl (p ⁻¹ᵁ s.inf K.UC))) c
    exact h1.trans h2.symm

/-- Composed with the base change isomorphism, the chart map of the family `Φ` is the restriction
map `Φ.appLE`. -/
theorem baseChangeEquiv_familyChartMap (s : Finset ι)
    (x : (curveCharts sC sU K hf pts).S s) :
    baseChangeEquiv sC H _ (isCompact_inf_UC sC K s).1 (isCompact_inf_UC sC K s).2
        (familyChartMap sC sU hf K pts A H Φ hΦ hle s x) = Φ.appLE _ _ (hle s) x :=
  RingEquiv.apply_symm_apply _ _

/-- The chart maps of the family `Φ` commute with the transition maps of the charts. -/
theorem familyChartMap_comm {s t : Finset ι} (h : s ⊆ t)
    (x : (curveCharts sC sU K hf pts).S s) :
    familyChartMap sC sU hf K pts A H Φ hΦ hle t
        ((curveCharts sC sU K hf pts).σ h x) =
      Algebra.TensorProduct.map
        ((curveCharts sC sU K hf pts).ρ h)
        (AlgHom.id k A.carrier) (familyChartMap sC sU hf K pts A H Φ hΦ hle s x) := by
  apply (baseChangeEquiv sC H _ (isCompact_inf_UC sC K t).1 (isCompact_inf_UC sC K t).2).injective
  rw [baseChangeEquiv_familyChartMap]
  refine Eq.trans ?_ (baseChangeEquiv_res sC H (Finset.inf_mono h) (isCompact_inf_UC sC K s).1
    (isCompact_inf_UC sC K s).2 _ _ _).symm
  rw [baseChangeEquiv_familyChartMap]
  exact (ConcreteCategory.congr_hom (Scheme.Hom.map_appLE Φ (hle t)
    (homOfLE (Finset.inf_mono h)).op) x).trans (ConcreteCategory.congr_hom
      (Scheme.Hom.appLE_map Φ (hle s)
        (homOfLE (Scheme.Hom.preimage_mono p (Finset.inf_mono h))).op) x).symm

omit [DecidableEq ι] [IsSeparated sC] [IsSeparated sU] [Smooth sU] [CompactSpace C]
  [QuasiSeparatedSpace C] in
/-- `appLE` only depends on the morphism. -/
theorem appLE_eq_of_eq {X X' : Scheme.{u}} {g g' : X ⟶ X'} (h : g = g') (V' : X'.Opens)
    (V : X.Opens) (e : V ≤ g ⁻¹ᵁ V') (e' : V ≤ g' ⁻¹ᵁ V') : g.appLE V' V e = g'.appLE V' V e' := by
  subst h; rfl

omit [DecidableEq ι] [IsSeparated sC] [IsSeparated sU] [Smooth sU] [CompactSpace C]
  [QuasiSeparatedSpace C] in
/-- The structure map of `Spec A` on global functions. -/
theorem specStructMap_appTop_inv (c : k) :
    (specStructMap (k := k) A.carrier).appTop ((Scheme.ΓSpecIso (.of k)).inv c) =
      (Scheme.ΓSpecIso (.of A.carrier)).inv (algebraMap k A.carrier c) :=
  (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap k A.carrier))) c).symm

omit [DecidableEq ι] [IsSeparated sC] [IsSeparated sU] [Smooth sU] [CompactSpace C]
  [QuasiSeparatedSpace C] in
/-- The map `appLE` of the identity morphism on an open `V` is the identity. -/
theorem appLE_id_self {X : Scheme.{u}} (V : X.Opens) (e : V ≤ (𝟙 X) ⁻¹ᵁ V) (a : Γ(X, V)) :
    (𝟙 X : X ⟶ X).appLE V V e a = a := by
  show X.presheaf.map (homOfLE (le_refl V)).op a = a
  rw [show (homOfLE (le_refl V)).op = 𝟙 (op V) from Subsingleton.elim _ _,
    CategoryTheory.Functor.map_id]
  rfl

/-- **The family reduces to `f` over the closed point.** -/
theorem familyChartMap_res (ιC : C ⟶ Y) (hιp : ιC ≫ p = 𝟙 C)
    (hιq : ιC ≫ q = sC ≫ Spec.map (CommRingCat.ofHom (toRes A).toRingHom)) (hιΦ : ιC ≫ Φ = f)
    (s : Finset ι) (x : (curveCharts sC sU K hf pts).S s) :
    Algebra.TensorProduct.map (AlgHom.id k ((curveCharts sC sU K hf pts).O s)) (toRes A)
        (familyChartMap sC sU hf K pts A H Φ hΦ hle s x) =
      (curveCharts sC sU K hf pts).f0 s x ⊗ₜ 1 := by
  letI := CurveMapCharts.sectionsAlgebra sC (s.inf K.UC)
  have hW : s.inf K.UC ≤ ιC ⁻¹ᵁ (p ⁻¹ᵁ s.inf K.UC) := by
    intro y hy
    show (ιC ≫ p).base y ∈ (s.inf K.UC : C.Opens)
    rw [hιp]; exact hy
  have key : ∀ z : Γ(C, s.inf K.UC) ⊗[k] A.carrier,
      Algebra.TensorProduct.rid k k Γ(C, s.inf K.UC)
          (Algebra.TensorProduct.map (AlgHom.id k Γ(C, s.inf K.UC)) (toRes A) z) =
        ιC.appLE _ _ hW (baseChangeEquiv sC H _ (isCompact_inf_UC sC K s).1
          (isCompact_inf_UC sC K s).2 z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    | tmul a c =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.rid_tmul,
        appLE_baseChangeEquiv_tmul sC H ιC _ _ _ hW a c]
      have e1 : (ιC ≫ p).appLE (s.inf K.UC) (s.inf K.UC) hW a = a :=
        (ConcreteCategory.congr_hom (appLE_eq_of_eq hιp _ _ hW le_rfl) a).trans
          (appLE_id_self _ _ a)
      have e2 : (ιC ≫ q).appLE ⊤ (s.inf K.UC) le_top ((Scheme.ΓSpecIso (.of A.carrier)).inv c) =
          algebraMap k Γ(C, s.inf K.UC) (toRes A c) := by
        have h3 : (Spec.map (CommRingCat.ofHom (toRes A).toRingHom)).appLE ⊤ ⊤ le_top
            ((Scheme.ΓSpecIso (.of A.carrier)).inv c) = (Scheme.ΓSpecIso (.of k)).inv (toRes A c) := by
          refine (ConcreteCategory.congr_hom (Scheme.Hom.appLE_preimage_self
            (Spec.map (CommRingCat.ofHom (toRes A).toRingHom)) ⊤) _).trans ?_
          exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
            (CommRingCat.ofHom (toRes A).toRingHom)) c).symm
        refine (ConcreteCategory.congr_hom (appLE_eq_of_eq hιq _ _ _ le_top) _).trans ?_
        refine (ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE sC
          (Spec.map (CommRingCat.ofHom (toRes A).toRingHom)) ⊤ ⊤ _ le_top le_top) _).symm.trans ?_
        change sC.appLE ⊤ (s.inf K.UC) _ ((Spec.map (CommRingCat.ofHom (toRes A).toRingHom)).appLE
          ⊤ ⊤ le_top ((Scheme.ΓSpecIso (.of A.carrier)).inv c)) = _
        rw [h3]
        change _ = (Stacks.Cech.baseRingHom sC (s.inf K.UC)).hom (toRes A c)
        rw [Stacks.Cech.baseRingHom_eq_appLE sC (s.inf K.UC) le_top]
        rfl
      rw [e1, e2, AlgHom.id_apply, Algebra.smul_def, mul_comm]
  change Algebra.TensorProduct.map (AlgHom.id k Γ(C, s.inf K.UC)) (toRes A)
      (familyChartMap sC sU hf K pts A H Φ hΦ hle s x) =
    (f.appLE (s.inf K.WU) (s.inf K.UC) (K.le_inf s) x) ⊗ₜ[k] (1 : k)
  apply (Algebra.TensorProduct.rid k k Γ(C, s.inf K.UC)).injective
  refine (key (familyChartMap sC sU hf K pts A H Φ hΦ hle s x)).trans ?_
  erw [baseChangeEquiv_familyChartMap]
  rw [Algebra.TensorProduct.rid_tmul, one_smul]
  refine (ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE ιC Φ _ _ _ (hle s) hW) x).trans ?_
  exact ConcreteCategory.congr_hom (appLE_eq_of_eq hιΦ _ _ _ (K.le_inf s)) x

/-- The value at a `k`-point, as a map of `k`-algebras. -/
def pointEvalₐ {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (P₀ : Spec (.of k) ⟶ X)
    (hP₀ : P₀ ≫ sX = 𝟙 _) {V : X.Opens} (hV : ⊤ ≤ P₀ ⁻¹ᵁ V) :
    letI := CurveMapCharts.sectionsAlgebra sX V
    Γ(X, V) →ₐ[k] k :=
  letI := CurveMapCharts.sectionsAlgebra sX V
  { toRingHom := CurveMapTangent.pointEval P₀ hV
    commutes' := fun c => CurveMapTangent.pointEval_baseRingHom P₀ sX hP₀ hV c }

omit [DecidableEq ι] [IsSeparated sC] [IsSeparated sU] [Smooth sU] [CompactSpace C]
  [QuasiSeparatedSpace C] in
/-- The `i`-th coordinate of `tensorEval ev y` in the basis `e` is `ev` applied to the `i`-th
coordinate `coordB e i y`. -/
theorem repr_tensorEval {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) {V : X.Opens}
    (ev : letI := CurveMapCharts.sectionsAlgebra sX V; Γ(X, V) →ₐ[k] k)
    (e : Module.Basis (Module.Free.ChooseBasisIndex k A.carrier) k A.carrier)
    (i : Module.Free.ChooseBasisIndex k A.carrier)
    (y : letI := CurveMapCharts.sectionsAlgebra sX V; Γ(X, V) ⊗[k] A.carrier) :
    letI := CurveMapCharts.sectionsAlgebra sX V
    e.repr (CurveMapTangent.tensorEval ev y) i = ev (coordB e i y) := by
  letI := CurveMapCharts.sectionsAlgebra sX V
  classical
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, Finsupp.add_apply, hx, hy, map_add, map_add]
  | tmul a c =>
    rw [CurveMapTangent.tensorEval_tmul, coordB_tmul, map_smul, ← Algebra.smul_def, map_smul,
      Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]

variable (P : Fin b → (Spec (.of k) ⟶ C)) (hP : ∀ β, P β ≫ sC = 𝟙 _)
  (PA : Fin b → (Spec (.of A.carrier) ⟶ Y))
  (hPAp : ∀ β, PA β ≫ p = specStructMap (k := k) A.carrier ≫ P β)
  (hPAq : ∀ β, PA β ≫ q = 𝟙 _)
  (hPAΦ : ∀ β, PA β ≫ Φ = specStructMap (k := k) A.carrier ≫ P β ≫ f)

include hPAp hPAq hPAΦ in
/-- **The family evaluated at a marked point is constant.** -/
theorem tensorEval_familyChartMap (β : Fin b) {s : Finset ι} (hV : ⊤ ≤ (P β) ⁻¹ᵁ (s.inf K.UC))
    (x : (curveCharts sC sU K hf pts).S s) :
    letI := CurveMapCharts.sectionsAlgebra sC (s.inf K.UC)
    CurveMapTangent.tensorEval (pointEvalₐ sC (P β) (hP β) hV)
        (familyChartMap sC sU hf K pts A H Φ hΦ hle s x) =
      algebraMap k A.carrier (pointEvalₐ sC (P β) (hP β) hV
        ((curveCharts sC sU K hf pts).f0 s x)) := by
  letI := CurveMapCharts.sectionsAlgebra sC (s.inf K.UC)
  have hW : ⊤ ≤ (PA β) ⁻¹ᵁ (p ⁻¹ᵁ s.inf K.UC) := by
    intro z _
    show (PA β ≫ p).base z ∈ (s.inf K.UC : C.Opens)
    rw [hPAp]
    exact hV (show (specStructMap (k := k) A.carrier).base z ∈ ⊤ from trivial)
  have hsA : ∀ y : Γ(Spec (.of k), ⊤), (specStructMap (k := k) A.carrier).appLE ⊤ ⊤ le_top y =
      (specStructMap (k := k) A.carrier).appTop y := fun y =>
    ConcreteCategory.congr_hom (Scheme.Hom.appLE_preimage_self _ ⊤) y
  have hsP : ⊤ ≤ (specStructMap (k := k) A.carrier ≫ P β) ⁻¹ᵁ (s.inf K.UC) :=
    fun z _ => hV (show (specStructMap (k := k) A.carrier).base z ∈ ⊤ from trivial)
  have hev : ∀ a : Γ(C, s.inf K.UC), (Scheme.ΓSpecIso (.of A.carrier)).inv
      (algebraMap k A.carrier (pointEvalₐ sC (P β) (hP β) hV a)) =
        (specStructMap (k := k) A.carrier ≫ P β).appLE (s.inf K.UC) ⊤ hsP a := by
    intro a
    rw [← specStructMap_appTop_inv]
    refine Eq.trans ?_ (ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE _ _ _ ⊤ ⊤ hV
      le_top) a)
    rw [CommRingCat.comp_apply, hsA]
    congr 1
    change (Scheme.ΓSpecIso (.of k)).inv ((Scheme.ΓSpecIso (.of k)).hom _) = _
    exact Iso.hom_inv_id_apply _ _
  have hq1 : ∀ y : Γ(Spec (.of A.carrier), ⊤), (PA β ≫ q).appLE ⊤ ⊤ le_top y = y := by
    intro y
    refine (ConcreteCategory.congr_hom (appLE_eq_of_eq (hPAq β) ⊤ ⊤ le_top le_top) y).trans ?_
    exact appLE_id_self _ _ y
  have key : ∀ z : Γ(C, s.inf K.UC) ⊗[k] A.carrier,
      (Scheme.ΓSpecIso (.of A.carrier)).inv
          (CurveMapTangent.tensorEval (pointEvalₐ sC (P β) (hP β) hV) z) =
        (PA β).appLE _ ⊤ hW (baseChangeEquiv sC H _ (isCompact_inf_UC sC K s).1
          (isCompact_inf_UC sC K s).2 z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    | tmul a c =>
      have e1 : (PA β ≫ p).appLE (s.inf K.UC) ⊤ hW a =
          (specStructMap (k := k) A.carrier ≫ P β).appLE (s.inf K.UC) ⊤ hsP a :=
        ConcreteCategory.congr_hom (appLE_eq_of_eq (hPAp β) (s.inf K.UC) ⊤ hW hsP) a
      rw [CurveMapTangent.tensorEval_tmul, map_mul, appLE_baseChangeEquiv_tmul sC H (PA β) _ _ _
        hW a c, hev a, e1, hq1]
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A.carrier)).inv).1
  refine (key (familyChartMap sC sU hf K pts A H Φ hΦ hle s x)).trans ?_
  erw [baseChangeEquiv_familyChartMap]
  refine Eq.trans ?_ (hev _).symm
  refine (ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE (PA β) Φ _ _ _ (hle s) hW)
    x).trans ?_
  refine (ConcreteCategory.congr_hom (appLE_eq_of_eq ((hPAΦ β).trans (Category.assoc _ _ _).symm)
    _ _ _ ((le_top.trans hsP).trans (fun z hz => K.le_inf s hz))) x).trans ?_
  exact (ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE
    (specStructMap (k := k) A.carrier ≫ P β) f _ (s.inf K.UC) ⊤ (K.le_inf s) hsP) x).symm

include hP hPAp hPAq hPAΦ in
/-- **The family reduces to `f` along the marked points.** -/
theorem familyChartMap_fix (hpts : ∀ β (z : Spec (.of k)), (P β).base z = pts β)
    (s : Finset ι) (x : (curveCharts sC sU K hf pts).S s) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k ((curveCharts sC sU K hf pts).𝔟 s))
        (AlgHom.id k A.carrier) (familyChartMap sC sU hf K pts A H Φ hΦ hle s x) =
      Ideal.Quotient.mk ((curveCharts sC sU K hf pts).𝔟 s)
        ((curveCharts sC sU K hf pts).f0 s x) ⊗ₜ 1 := by
  classical
  letI := CurveMapCharts.sectionsAlgebra sC (s.inf K.UC)
  set e := Module.Free.chooseBasis k A.carrier
  refine ext_coordB e fun i => ?_
  rw [coordB_map, coordB_tmul]
  change Ideal.Quotient.mk _ _ = _
  rw [← Ideal.Quotient.mkₐ_eq_mk k, ← map_smul, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq]
  refine (CurveMapCharts.mem_vanishingIdeal pts (s.inf K.UC) _).2 ?_
  intro β hβ
  have hV : ⊤ ≤ (P β) ⁻¹ᵁ (s.inf K.UC) := by
    intro z _
    show (P β).base z ∈ (s.inf K.UC : C.Opens)
    rw [hpts]; exact hβ
  set pt0 : Spec (.of k) := IsLocalRing.closedPoint k
  have hpt : (P β).base pt0 ∈ s.inf K.UC := hV trivial
  set ev := pointEvalₐ sC (P β) (hP β) hV
  have h0 : CurveMapTangent.pointEval (P β) hV
      (coordB e i (familyChartMap sC sU hf K pts A H Φ hΦ hle s x) -
        e.repr 1 i • (curveCharts sC sU K hf pts).f0 s x) = 0 := by
    change ev (_ - _) = 0
    erw [map_sub, map_smul]
    have h1 := repr_tensorEval A sC ev e i (familyChartMap sC sU hf K pts A H Φ hΦ hle s x)
    rw [tensorEval_familyChartMap sC sU hf K pts A H Φ hΦ hle P hP PA hPAp hPAq hPAΦ β hV x,
      Algebra.algebraMap_eq_smul_one, map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
    erw [← h1]
    rw [smul_eq_mul, mul_comm, sub_self]
  have hm := mem_maximalIdeal_of_pointEval_eq_zero (P β) hV pt0 hpt _ h0
  have key : ∀ (y : C) (hy : y ∈ s.inf K.UC), y = (P β).base pt0 →
      C.presheaf.germ _ y hy (coordB e i (familyChartMap sC sU hf K pts A H Φ hΦ hle s x) -
        e.repr 1 i • (curveCharts sC sU K hf pts).f0 s x) ∈
        IsLocalRing.maximalIdeal (C.presheaf.stalk y) := by
    rintro y hy rfl
    exact hm
  exact key _ hβ (hpts β pt0).symm

/-- **The point on the charts of a family `Φ : C ×ₖ Spec A ⟶ U`** reducing to `f` over the closed
point and constant along the marked points. -/
def familyCurvePoint (ιC : C ⟶ Y) (hιp : ιC ≫ p = 𝟙 C)
    (hιq : ιC ≫ q = sC ≫ Spec.map (CommRingCat.ofHom (toRes A).toRingHom)) (hιΦ : ιC ≫ Φ = f)
    (hpts : ∀ β (z : Spec (.of k)), (P β).base z = pts β) :
    CurvePoint (curveCharts sC sU K hf pts) A where
  pt s := familyChartMap sC sU hf K pts A H Φ hΦ hle s
  pt_comm h x := familyChartMap_comm sC sU hf K pts A H Φ hΦ hle h x
  pt_res s x := familyChartMap_res sC sU hf K pts A H Φ hΦ hle ιC hιp hιq hιΦ s x
  pt_fix s x := familyChartMap_fix sC sU hf K pts A H Φ hΦ hle P hP PA hPAp hPAq hPAΦ hpts s x

omit [IsSeparated sC] [IsSeparated sU] [Smooth sU] [CompactSpace C] [QuasiSeparatedSpace C]
  [DecidableEq ι] in
/-- A family over a one-point base whose closed fibre is `f` maps the base change of the source
charts into the target charts. -/
theorem preimage_le_of_section {Φ' : Y ⟶ U} (ιC : C ⟶ Y) (hιΦ : ιC ≫ Φ' = f)
    (hsurj : ∀ y, ιC.base (p.base y) = y) (s : Finset ι) :
    p ⁻¹ᵁ s.inf K.UC ≤ Φ' ⁻¹ᵁ s.inf K.WU := by
  intro y hy
  rw [← hsurj y]
  show (ιC ≫ Φ').base (p.base y) ∈ (s.inf K.WU : U.Opens)
  rw [hιΦ]
  exact K.le_inf s hy

open Stacks.TwistPullbackPinned Stacks.AmpleProjectiveImmersion in
/-- **The frames of a family of curve maps given by a tuple of coefficients.** Let
`Φ : C ×ₖ Spec A ⟶ U` be a family with a pinned isomorphism `(Φ ≫ g_U)^* 𝒪(1) ≅ p^* L`
(`L = g_C^* 𝒪(1)`) carrying the coordinates to the sections `Σⱼ cA_{m j} wⱼ`. On each chart, the
local expressions `Σⱼ (wⱼ / σ_{l t}) ⊗ cA_{m j}` are a unit `fr` times the images of the chart
coordinates `x_{m t} = σ_m / σ_{l t}` of the target. -/
theorem exists_frames_familyChartMap {d : ℕ} (gC : C ⟶ projectiveSpaceAtUniverse.{u} d)
    (gU : U ⟶ projectiveSpaceAtUniverse.{u} d) (l : ι → Fin (d + 1))
    (hσC : ∀ t, K.UC t ≤ nvCover (pullbackCoordSection.{u} gC) (l t))
    (hσU : ∀ t, K.WU t ≤ nvCover (pullbackCoordSection.{u} gU) (l t))
    {N : ℕ} (w : Fin N → Γ((Scheme.Modules.pullback gC).obj (twistingSheafAtUniverse.{u} d), ⊤))
    (cA : Fin (d + 1) → Fin N → A.carrier)
    (gA : Y ⟶ projectiveSpaceAtUniverse.{u} d) (hgA : gA = Φ ≫ gU)
    (α : (Scheme.Modules.pullback gA).obj (twistingSheafAtUniverse.{u} d) ⟶
      (Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback gC).obj
        (twistingSheafAtUniverse.{u} d))) [IsIso α]
    (hα : ∀ m, α.app ⊤ (pullbackCoordSection.{u} gA m) =
      Stacks.LinearSystemScheme.coordSection p q _ w
        (fun j => (Scheme.ΓSpecIso (.of A.carrier)).inv (cA m j)))
    (t : ι) :
    ∃ fr : ((curveCharts sC sU K hf pts).O {t} ⊗[k] A.carrier)ˣ, ∀ m',
      ∑ j', localSection sC sU hf K pts _ l hσC (w j') t ⊗ₜ[k] cA m' j' =
        fr * familyChartMap sC sU hf K pts A H Φ hΦ hle {t} (chartCoord _ K.WU l hσU m' t) := by
  classical
  have hct := isCompact_inf_UC sC K ({t} : Finset ι)
  letI := CurveMapCharts.sectionsAlgebra sC (({t} : Finset ι).inf K.UC)
  letI := Stacks.InvertiblePullback.isInvertibleModule_pullback p
    ((Scheme.Modules.pullback gC).obj (twistingSheafAtUniverse.{u} d))
  have hσCt : ({t} : Finset ι).inf K.UC ≤ nvOpen _ (pullbackCoordSection.{u} gC (l t)) :=
    inf_le_nvCover _ K.UC l hσC (Finset.mem_singleton_self t)
  have hσUt : ({t} : Finset ι).inf K.WU ≤ nvOpen _ (pullbackCoordSection.{u} gU (l t)) :=
    inf_le_nvCover _ K.WU l hσU (Finset.mem_singleton_self t)
  have hVA : p ⁻¹ᵁ (({t} : Finset ι).inf K.UC) ≤ nvOpen _ (pullbackCoordSection.{u} gA (l t)) := by
    intro y hy
    have h1 := hσUt (hle {t} hy)
    rw [← SetLike.mem_coe, Stacks.NonvanishingOpen.coe_nonvanishingOpen,
      mem_nonvanishingLocus_pullbackCoordSection_iff] at h1 ⊢
    rw [hgA]
    exact h1
  have hζ : p ⁻¹ᵁ (({t} : Finset ι).inf K.UC) ≤
      nvOpen _ (α.app ⊤ (pullbackCoordSection.{u} gA (l t))) := by
    rw [show α = (asIso α).hom from rfl, nvOpen_iso_app]
    exact hVA
  have hσh : p ⁻¹ᵁ (({t} : Finset ι).inf K.UC) ≤ nvOpen _ (pullbackGlobalSections p _
      (pullbackCoordSection.{u} gC (l t))) := by
    rw [Stacks.RatioPullback.nvOpen_pullbackGlobalSections]
    exact fun y hy => hσCt hy
  set e := baseChangeEquiv sC H _ hct.1 hct.2 with he
  set u : Fin (d + 1) → Γ(Y, p ⁻¹ᵁ (({t} : Finset ι).inf K.UC)) := fun m' =>
    e (∑ j', localSection sC sU hf K pts _ l hσC (w j') t ⊗ₜ[k] cA m' j' :
      (curveCharts sC sU K hf pts).O {t} ⊗[k] A.carrier) with hudef
  have hu : ∀ m', resT (p ⁻¹ᵁ (({t} : Finset ι).inf K.UC)) (α.app ⊤ (pullbackCoordSection.{u} gA m')) =
      u m' • resT (p ⁻¹ᵁ (({t} : Finset ι).inf K.UC)) (pullbackGlobalSections p _ (pullbackCoordSection.{u} gC (l t))) := by
    intro m'
    rw [hα m']
    exact resT_coordSection_eq_smul sC H _ w (cA m') _ hσCt hct.1 hct.2
  set r : Fin (d + 1) → Γ(Y, p ⁻¹ᵁ (({t} : Finset ι).inf K.UC)) := fun m' =>
    div _ hζ (resT (p ⁻¹ᵁ (({t} : Finset ι).inf K.UC)) (α.app ⊤ (pullbackCoordSection.{u} gA m'))) with hrdef
  have hr : ∀ m', e (familyChartMap sC sU hf K pts A H Φ hΦ hle {t}
      (chartCoord _ K.WU l hσU m' t)) = r m' := by
    intro m'
    refine (baseChangeEquiv_familyChartMap sC sU hf K pts A H Φ hΦ hle {t} _).trans ?_
    refine Eq.trans ?_ (div_iso_app (asIso α) _ _ hVA hζ).symm
    have hx : chartCoord _ K.WU l hσU m' t = div _ hσUt
        (resT _ (pullbackCoordSection.{u} gU m')) := by
      rw [chartCoord, ratio, CurveMapCharts.resO_div, resM_resT]
    rw [hx]
    exact CurveMapTangent.appLE_div_pullbackCoordSection Φ gU gA hgA (hle {t}) (l t) m' hσUt hVA
  have hrs : ∀ m', r m' • resT (p ⁻¹ᵁ (({t} : Finset ι).inf K.UC)) (α.app ⊤ (pullbackCoordSection.{u} gA (l t))) =
      resT (p ⁻¹ᵁ (({t} : Finset ι).inf K.UC)) (α.app ⊤ (pullbackCoordSection.{u} gA m')) := fun m' => div_smul _ _ _
  have hum : ∀ m', u m' = r m' * u (l t) := by
    intro m'
    refine eq_of_smul_eq_smul _ hσh ?_
    rw [← hu m', mul_smul, ← hu (l t), hrs m']
  have hw0 : div _ hζ (resT (p ⁻¹ᵁ (({t} : Finset ι).inf K.UC)) (pullbackGlobalSections p _ (pullbackCoordSection.{u} gC (l t)))) *
      u (l t) = 1 := by
    refine eq_of_smul_eq_smul _ hσh ?_
    rw [mul_smul, ← hu (l t), div_smul, one_smul]
  have hunit : IsUnit (∑ j', localSection sC sU hf K pts _ l hσC (w j') t ⊗ₜ[k] cA (l t) j' :
      (curveCharts sC sU K hf pts).O {t} ⊗[k] A.carrier) := by
    have h1 : IsUnit (u (l t)) := isUnit_iff_exists_inv.2 ⟨_, (mul_comm _ _).trans hw0⟩
    exact (MulEquiv.isUnit_map e.toMulEquiv).1 h1
  refine ⟨hunit.unit, fun m' => ?_⟩
  apply e.injective
  refine Eq.trans ?_ (e.map_mul _ _).symm
  refine (hum m').trans ((mul_comm _ _).trans ?_)
  rw [← hr m']
  rfl

end FamilyCurvePoint

end MMP.Fourfold.CurveMapSections
