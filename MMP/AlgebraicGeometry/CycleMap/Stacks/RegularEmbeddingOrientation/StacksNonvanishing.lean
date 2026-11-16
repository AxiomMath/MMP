module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.StacksPresentation
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ClassicalTopologyCharts

/-!
# The section `σ̄` vanishes only on `X` near `X`, for Stacks vector bundles

Let `i : X → Y` be a regular imbedding of codimension `d` of complex schemes, `σ : Y ⟶ 𝐕(ℰ)` a
section of the vector bundle of a quasi-coherent `𝒪_Y`-module `ℰ`, finite locally free of rank
`e`, with zero scheme `X`, and `𝐕(ℰ)(ℂ)|_V → Q` a surjective morphism of complex topological
vector bundles on an open `V ⊇ X(ℂ)` whose kernel `C` is complementary to the normal bundle `N`
along `X`. Then the induced section `σ̄` of `Q` vanishes on no point of `V - X` near `X`
(Fulton, §19.2): near a point `x ∈ X(ℂ)`, `σ = M f` with `f` a regular sequence cutting out `X`,
so `σ̄ = L M f`, and `L(y) M(y)` is injective at `y = x` (`N_x = range M(x)`, `M(x)` injective and
`ker L(x) ∩ N_x = 0`), hence for `y` near `x`.

## Main results

* `MMP.Modules.mapFun_eq_chartInv_coord`: `σ(y)` is the point of the chart over `y` with the
  coordinates of `σ(y)`.
* `MMP.Modules.mem_range_map_of_coord_eq_zero`: a point at which all chart coordinates of `σ`
  vanish lies on `Z(σ)`.
* `MMP.Modules.injective_comp_evalMatrix`: `L(x) M(x)` is injective.
* `MMP.Modules.exists_isOpen_sectionBar_mem_range_zeroSection`: an open neighbourhood of `X(ℂ)`
  on which `σ̄` vanishes only on `X(ℂ)`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Bundle Topology Filter
open scoped Matrix

namespace MMP.Modules

open UnderlyingSpace
open Stacks.AlgebraicGeometry.RegularIdealSheaf (IsRegularClosedImmersionOfCodim)

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))] {e d : ℕ}
  {E : Y.Modules} [E.IsQuasicoherent]

section Points

variable {σ : Y ⟶ totalSpace E} [σ.IsOver (Spec (.of ℂ))]

/-- A section maps `V(ℂ)` into `π⁻¹V(ℂ)`. -/
lemma top_le_preimage_mapFun_section (hσ : σ ≫ proj E = 𝟙 Y) {U : Y.Opens}
    {y : UnderlyingSpace ℂ Y} (hy : ⊤ ≤ y.toHom ⁻¹ᵁ U) :
    ⊤ ≤ (mapFun σ y).toHom ⁻¹ᵁ (proj E ⁻¹ᵁ U) := by
  rwa [toHom_mapFun, Scheme.Hom.comp_preimage, preimage_preimage_proj_of_comp_eq_id hσ]

private lemma chartInv_congr (c : Chart E e) {y y' : UnderlyingSpace ℂ Y} (h : y' = y)
    (hy : ⊤ ≤ y.toHom ⁻¹ᵁ c.1.1) (hy' : ⊤ ≤ y'.toHom ⁻¹ᵁ c.1.1) (w : Fin e → ℂ) :
    chartInv c y' hy' w = chartInv c y hy w := by
  subst h
  rfl

/-- The point `σ(y)` is the point of the chart `c` over `y` with the coordinates of `σ(y)`. -/
lemma mapFun_eq_chartInv_coord (hσ : σ ≫ proj E = 𝟙 Y) (c : Chart E e)
    (y : UnderlyingSpace ℂ Y) (hy : ⊤ ≤ y.toHom ⁻¹ᵁ c.1.1) :
    mapFun σ y = chartInv c y hy (coord c (mapFun σ y)) :=
  (chartInv_mapFun_proj_coord c _ (top_le_preimage_mapFun_section hσ hy)).symm.trans
    (chartInv_congr c (mapFun_proj_mapFun_section hσ y) _ _ _)

/-- A point of `V(ℂ)`, `c = (V, b)`, at which all the chart coordinates of `σ` vanish lies on
`Z(σ)`. -/
theorem mem_range_map_of_coord_eq_zero (i : X ⟶ Y) [i.IsOver (Spec (.of ℂ))]
    [IsClosedImmersion i] (hσ : σ ≫ proj E = 𝟙 Y) (hs : zeroLocus E σ = i.ker) (c : Chart E e)
    (y : UnderlyingSpace ℂ Y) (hy : ⊤ ≤ y.toHom ⁻¹ᵁ c.1.1) (h0 : coord c (mapFun σ y) = 0) :
    y ∈ Set.range (UnderlyingSpace.map (K := ℂ) i) := by
  change y ∈ Set.range (mapFun (K := ℂ) i)
  rw [range_mapFun_of_isClosedImmersion]
  have hq : y.toHom (IsLocalRing.closedPoint ℂ) ∈ c.1.1 := (top_le_preimage_iff y _).1 hy
  obtain ⟨_, ⟨W, hW, rfl⟩, hqW, hWle⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hq c.1.1.2
  have hyW : ⊤ ≤ y.toHom ⁻¹ᵁ W := (top_le_preimage_iff y _).2 hqW
  have hWle' : W ≤ σ ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1) := by
    rwa [preimage_preimage_proj_of_comp_eq_id hσ]
  have hsupp : y.toHom (IsLocalRing.closedPoint ℂ) ∈ i.ker.support := by
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨W, hW⟩) hqW, ← hs,
      ideal_zeroLocus σ c ⟨W, hW⟩ hWle', Scheme.mem_zeroLocus_iff]
    intro g hg hqg
    refine (top_le_preimage_basicOpen_iff y hyW g).1 ((top_le_preimage_iff y _).2 hqg)
      (RegularSequenceFibre.ev_eq_zero_of_mem_span (evalRingHom y hyW) (fun a ↦ ?_) hg)
    rw [evalRingHom_apply, eval_sectionCoord, h0]
    rfl
  have h2 : y.toHom (IsLocalRing.closedPoint ℂ) ∈ closure (Set.range i) := by
    rwa [← Scheme.Hom.support_ker]
  rwa [i.isClosedEmbedding.isClosed_range.closure_eq] at h2

end Points

variable {σ : Y ⟶ totalSpace E} {c : Chart E e} {x : UnderlyingSpace ℂ Y} {W : Y.Opens}
  {hWc : W ≤ σ ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1)} {hxW : ⊤ ≤ x.toHom ⁻¹ᵁ W} {f : Fin d → Γ(Y, W)}
  {M : Fin e → Fin d → Γ(Y, W)} {G : Fin d → Fin e → Γ(Y, W)}

/-- `M(x)` is injective for a local regular presentation. -/
lemma injective_evalMatrix (h : IsLocalRegularPresentation σ c x hWc hxW M G f) :
    Function.Injective (evalMatrix x hxW M) := by
  intro v v' hvv'
  funext b
  have key : ∀ u : Fin d → ℂ, evalMatrix x hxW G (evalMatrix x hxW M u) b = u b := fun u ↦ by
    simp only [evalMatrix_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul, eval_mul_eval_eq_one h, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← key v, ← key v', hvv']

/-- **`L(x) M(x)` is injective.** If the kernel of a linear map `L` on `ℂᵉ` is a complement of
the normal fibre `N_x`, then `L ∘ M(x)` is injective, for a local regular presentation at `x`. -/
theorem injective_comp_evalMatrix (h : IsLocalRegularPresentation σ c x hWc hxW M G f)
    {P : Type*} [AddCommGroup P] [Module ℂ P] (L : (Fin e → ℂ) →ₗ[ℂ] P)
    (hL : IsCompl (LinearMap.ker L) (normalFibre σ c x)) :
    Function.Injective (L ∘ₗ evalMatrix x hxW M) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have hmem : evalMatrix x hxW M v ∈ LinearMap.ker L ⊓ normalFibre σ c x :=
    ⟨hv, normalFibre_eq_range h ▸ ⟨v, rfl⟩⟩
  rw [hL.inf_eq_bot, Submodule.mem_bot] at hmem
  exact injective_evalMatrix h (hmem.trans (map_zero _).symm)

section Nonvanishing

variable [SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E e]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {N : Set (UnderlyingSpace ℂ Y)} {Q : N → Type} [∀ y, AddCommGroup (Q y)]
  [∀ y, Module ℂ (Q y)] [∀ y, TopologicalSpace (Q y)] [TopologicalSpace (TotalSpace F Q)]
  [FiberBundle F Q] [_root_.VectorBundle ℂ F Q]

/-- A linear trivialization is injective on each fibre over its base set. -/
lemma injective_linearMapAt
    (τ : Trivialization F (TotalSpace.proj : TotalSpace F Q → N)) [τ.IsLinear ℂ] {b : N}
    (hb : b ∈ τ.baseSet) : Function.Injective (τ.linearMapAt ℂ b) := by
  intro v v' h
  rw [τ.coe_linearMapAt_of_mem hb] at h
  have := congrArg (τ.symm b) h
  rwa [τ.symm_apply_apply_mk hb, τ.symm_apply_apply_mk hb] at this

/-- **`σ̄` vanishes only on `X` near a point of `X`.** Let `i` be a regular imbedding, `σ` a
section of `𝐕(ℰ)` with `Z(σ) = X`, and `𝐕(ℰ)(ℂ)|_N → Q` a continuous morphism of bundles on an
open `N`, complex linear on the fibres in the chart coordinates, whose kernel at the points of
`X(ℂ)` is a complement of the normal fibre. Then every point `i(x) ∈ N` has a neighbourhood `O`
such that the induced section `σ̄` of `Q` vanishes on `O ∩ N` only at points of `X(ℂ)`. -/
theorem exists_mem_nhds_sectionBar_mem_range_zeroSection (i : X ⟶ Y) [i.IsOver (Spec (.of ℂ))]
    [IsClosedImmersion i] (hi : IsRegularClosedImmersionOfCodim i d) (σ : Y ⟶ totalSpace E)
    [σ.IsOver (Spec (.of ℂ))]
    (hσ : σ ≫ proj E = 𝟙 Y) (hs : zeroLocus E σ = i.ker) (hN : IsOpen N)
    (quot : {p : UnderlyingSpace ℂ (totalSpace E) // mapFun (proj E) p ∈ N} → TotalSpace F Q)
    (hquot : Continuous quot)
    (hfibre : ∀ (c : Chart E e) (y : UnderlyingSpace ℂ Y) (hy : ⊤ ≤ y.toHom ⁻¹ᵁ c.1.1)
      (hyN : y ∈ N), ∃ L : (Fin e → ℂ) →ₗ[ℂ] Q ⟨y, hyN⟩,
        (∀ w, quot ⟨chartInv c y hy w, by rwa [mapFun_proj_chartInv]⟩ = ⟨⟨y, hyN⟩, L w⟩) ∧
        Function.Surjective L ∧
        (y ∈ Set.range (UnderlyingSpace.map i) → IsCompl (LinearMap.ker L) (normalFibre σ c y)))
    (x : UnderlyingSpace ℂ X) (hxN : mapFun i x ∈ N) :
    ∃ O ∈ 𝓝 (mapFun i x), ∀ y : N, y.1 ∈ O →
      quot ⟨mapFun σ y, by rw [mapFun_proj_mapFun_section hσ]; exact y.2⟩ ∈
          Set.range (Bundle.zeroSection F Q) →
        y.1 ∈ Set.range (UnderlyingSpace.map (K := ℂ) i) := by
  classical
  choose L hL _hsurj hC using hfibre
  set x₀ := mapFun i x
  set c := chartAt E e x₀
  have hxc : ⊤ ≤ x₀.toHom ⁻¹ᵁ c.1.1 := mem_chartBase_chartAt E e x₀
  obtain ⟨W, hWc, hxW, M, G, f, hP⟩ := exists_isLocalRegularPresentation i hi σ hσ hs c x hxc
  have hWc' : W ≤ c.1.1 := hWc.trans (preimage_preimage_proj_of_comp_eq_id hσ _).le
  let b₀ : N := ⟨x₀, hxN⟩
  let τ := trivializationAt F Q b₀
  have hb₀ : b₀ ∈ τ.baseSet := FiberBundle.mem_baseSet_trivializationAt F Q b₀
  let O₀ : Set (UnderlyingSpace ℂ Y) :=
    (Subtype.val '' τ.baseSet) ∩ {y | ⊤ ≤ y.toHom ⁻¹ᵁ W}
  have hO₀ : IsOpen O₀ :=
    (hN.isOpenMap_subtype_val _ τ.open_baseSet).inter (isOpen_setOf_le_preimage W)
  have hxO₀ : x₀ ∈ O₀ := ⟨⟨b₀, hb₀, rfl⟩, hxW⟩
  have memN : ∀ y : O₀, y.1 ∈ N := fun y ↦ by
    obtain ⟨⟨b, -, hb⟩, -⟩ := y.2
    exact hb ▸ b.2
  have memB : ∀ y : O₀, (⟨y.1, memN y⟩ : N) ∈ τ.baseSet := fun y ↦ by
    obtain ⟨⟨b, hb, hby⟩, -⟩ := y.2
    have : b = ⟨y.1, memN y⟩ := Subtype.ext hby
    exact this ▸ hb
  have memW : ∀ y : O₀, ⊤ ≤ y.1.toHom ⁻¹ᵁ W := fun y ↦ y.2.2
  have memj : ∀ y : O₀, ⊤ ≤ y.1.toHom ⁻¹ᵁ c.1.1 := fun y ↦
    (memW y).trans (Scheme.Hom.preimage_mono _ hWc')
  let q : O₀ × (Fin e → ℂ) → TotalSpace F Q := fun z ↦
    quot ⟨chartInv c z.1.1 (memj z.1) z.2, by rw [mapFun_proj_chartInv]; exact memN z.1⟩
  have hq : ∀ z, q z = ⟨⟨z.1.1, memN z.1⟩, L c z.1.1 (memj z.1) (memN z.1) z.2⟩ := fun z ↦
    hL c z.1.1 (memj z.1) (memN z.1) z.2
  let Φ : O₀ × (Fin e → ℂ) → F := fun z ↦ (τ (q z)).2
  have hΦ : Continuous Φ := by
    have h1 : Continuous q :=
      hquot.comp (((continuous_chartInv c).comp
        (((continuous_subtype_val.comp continuous_fst).subtype_mk
          (fun z : O₀ × (Fin e → ℂ) ↦ memj z.1)).prodMk continuous_snd)).subtype_mk _)
    refine continuous_snd.comp (τ.continuousOn.comp_continuous h1 fun z ↦ ?_)
    rw [τ.mem_source, hq]
    exact memB z.1
  let Λ : ∀ y : O₀, (Fin e → ℂ) →ₗ[ℂ] F := fun y ↦
    τ.linearMapAt ℂ ⟨y.1, memN y⟩ ∘ₗ L c y.1 (memj y) (memN y)
  have hΛ : ∀ y w, Φ (y, w) = Λ y w := fun y w ↦ by
    simp only [Φ, Λ, LinearMap.comp_apply, hq, τ.coe_linearMapAt_of_mem (memB y)]
  let y₀ : O₀ := ⟨x₀, hxO₀⟩
  have hinj : Function.Injective (Λ y₀ ∘ₗ evalMatrix x₀ hxW M) := by
    have h1 := injective_comp_evalMatrix hP (L c x₀ (memj y₀) (memN y₀))
      (hC c x₀ (memj y₀) (memN y₀) ⟨x, rfl⟩)
    exact (injective_linearMapAt τ (memB y₀)).comp h1
  obtain ⟨P, hPinv⟩ := LinearMap.exists_leftInverse_of_injective _
    (LinearMap.ker_eq_bot.2 hinj)
  let mcol : O₀ → Fin d → Fin e → ℂ := fun y c a ↦ eval y.1 (memW y) (M a c)
  let A : O₀ → Matrix (Fin d) (Fin d) ℂ := fun y b c ↦ P (Φ (y, mcol y c)) b
  have hW' : Continuous fun y : O₀ ↦
      (⟨y.1, memW y⟩ : {p : UnderlyingSpace ℂ Y // ⊤ ≤ p.toHom ⁻¹ᵁ W}) :=
    continuous_subtype_val.subtype_mk memW
  have hev : ∀ a c, Continuous fun y : O₀ ↦ eval (K := ℂ) y.1 (memW y) (M a c) := fun a c ↦ by
    have h := (continuous_eval (K := ℂ) W (M a c)).comp hW'
    exact h
  have hmcol : ∀ c, Continuous fun y ↦ mcol y c := fun c ↦ continuous_pi fun a ↦ hev a c
  have hA : Continuous A := continuous_pi fun b ↦ continuous_pi fun c ↦
    (continuous_apply b).comp (P.continuous_of_finiteDimensional.comp
      (hΦ.comp (continuous_id.prodMk (hmcol c))))
  have hA₀ : (A y₀).det ≠ 0 := by
    have : A y₀ = 1 := by
      funext b c
      have hc : mcol y₀ c = evalMatrix x₀ hxW M (Pi.single c 1) := by
        funext a
        simp [mcol, evalMatrix_apply, Pi.single_apply]
        rfl
      have := congrFun (LinearMap.congr_fun hPinv (Pi.single c 1)) b
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
      simp only [A, hc, hΛ, this, Matrix.one_apply, Pi.single_apply, eq_comm]
    simp [this]
  have hev := hA.matrix_det.continuousAt.eventually_ne hA₀
  refine ⟨Subtype.val '' {y : O₀ | (A y).det ≠ 0},
    hO₀.isOpenEmbedding_subtypeVal.image_mem_nhds.2 hev, ?_⟩
  rintro ⟨yv, hyv⟩ ⟨z, hz, rfl⟩ hzero
  let w : Fin e → ℂ := coord c (mapFun σ z.1)
  have hsz : quot ⟨mapFun σ z.1, by rw [mapFun_proj_mapFun_section hσ]; exact hyv⟩ = q (z, w) :=
    congrArg quot (Subtype.ext (mapFun_eq_chartInv_coord hσ c z.1 (memj z)))
  obtain ⟨b, hb⟩ := hzero
  rw [hsz, hq] at hb
  obtain rfl : b = ⟨z.1, memN z⟩ := congrArg TotalSpace.proj hb
  have hLw : L c z.1 (memj z) (memN z) w = 0 := (TotalSpace.mk_inj.1 hb).symm
  have hΦw : Φ (z, w) = 0 := by
    rw [hΛ]
    simp [Λ, hLw]
  let fz : Fin d → ℂ := fun c ↦ eval z.1 (memW z) (f c)
  have hw : w = ∑ c, fz c • mcol z c := by
    funext a
    have := congrArg (evalRingHom z.1 (memW z)) (hP.eq_M a)
    simp only [map_sum, map_mul, evalRingHom_apply] at this
    rw [eval_sectionCoord] at this
    refine this.trans ?_
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    simp only [Pi.smul_apply, smul_eq_mul, fz, mcol]
    exact mul_comm _ _
  have hAf : A z *ᵥ fz = 0 := by
    funext b
    have : Φ (z, w) = ∑ c, fz c • Φ (z, mcol z c) := by
      rw [hΛ, hw, map_sum]
      simp only [map_smul, hΛ]
    have h2 := congrFun (congrArg P this) b
    rw [hΦw, map_zero, map_sum] at h2
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
    rw [Pi.zero_apply] at h2
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    exact (Finset.sum_congr rfl fun c _ ↦ mul_comm _ _).trans h2.symm
  have hf0 := Matrix.eq_zero_of_mulVec_eq_zero hz hAf
  refine mem_range_map_of_coord_eq_zero i hσ hs c z.1 (memj z) ?_
  change w = 0
  rw [hw, hf0]
  simp

/-- **`σ̄` vanishes exactly on `X` near `X`.** In the situation of
`exists_mem_nhds_sectionBar_mem_range_zeroSection`, with `X(ℂ) ⊆ N`, there is an open
neighbourhood `V ⊆ N` of `X(ℂ)` on which `σ̄` vanishes only at the points of `X(ℂ)`. -/
theorem exists_isOpen_sectionBar_mem_range_zeroSection (i : X ⟶ Y) [i.IsOver (Spec (.of ℂ))]
    [IsClosedImmersion i] (hi : IsRegularClosedImmersionOfCodim i d) (σ : Y ⟶ totalSpace E)
    [σ.IsOver (Spec (.of ℂ))]
    (hσ : σ ≫ proj E = 𝟙 Y) (hs : zeroLocus E σ = i.ker) (hN : IsOpen N)
    (hXN : Set.range (UnderlyingSpace.map (K := ℂ) i) ⊆ N)
    (quot : {p : UnderlyingSpace ℂ (totalSpace E) // mapFun (proj E) p ∈ N} → TotalSpace F Q)
    (hquot : Continuous quot)
    (hfibre : ∀ (c : Chart E e) (y : UnderlyingSpace ℂ Y) (hy : ⊤ ≤ y.toHom ⁻¹ᵁ c.1.1)
      (hyN : y ∈ N), ∃ L : (Fin e → ℂ) →ₗ[ℂ] Q ⟨y, hyN⟩,
        (∀ w, quot ⟨chartInv c y hy w, by rwa [mapFun_proj_chartInv]⟩ = ⟨⟨y, hyN⟩, L w⟩) ∧
        Function.Surjective L ∧
        (y ∈ Set.range (UnderlyingSpace.map i) → IsCompl (LinearMap.ker L) (normalFibre σ c y))) :
    ∃ V ⊆ N, IsOpen V ∧ Set.range (UnderlyingSpace.map (K := ℂ) i) ⊆ V ∧ ∀ y : N, y.1 ∈ V →
      quot ⟨mapFun σ y, by rw [mapFun_proj_mapFun_section hσ]; exact y.2⟩ ∈
          Set.range (Bundle.zeroSection F Q) →
        y.1 ∈ Set.range (UnderlyingSpace.map (K := ℂ) i) := by
  have hO : ∀ x : UnderlyingSpace ℂ X, ∃ O : Set (UnderlyingSpace ℂ Y), IsOpen O ∧
      mapFun i x ∈ O ∧ ∀ y : N, y.1 ∈ O →
        quot ⟨mapFun σ y, by rw [mapFun_proj_mapFun_section hσ]; exact y.2⟩ ∈
          Set.range (Bundle.zeroSection F Q) →
        y.1 ∈ Set.range (UnderlyingSpace.map (K := ℂ) i) := fun x ↦ by
    obtain ⟨O, hO, hOs⟩ := exists_mem_nhds_sectionBar_mem_range_zeroSection i hi σ hσ hs hN quot
      hquot hfibre x (hXN ⟨x, rfl⟩)
    obtain ⟨O', hO'O, hO', hxO'⟩ := mem_nhds_iff.1 hO
    exact ⟨O', hO', hxO', fun y hy ↦ hOs y (hO'O hy)⟩
  choose O hOopen hxO hOs using hO
  refine ⟨N ∩ ⋃ x, O x, Set.inter_subset_left, hN.inter (isOpen_iUnion hOopen), ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨hXN ⟨x, rfl⟩, Set.mem_iUnion.2 ⟨x, hxO x⟩⟩
  · rintro y ⟨-, hy⟩
    obtain ⟨x, hx⟩ := Set.mem_iUnion.1 hy
    exact hOs x y hx

end Nonvanishing

end MMP.Modules
