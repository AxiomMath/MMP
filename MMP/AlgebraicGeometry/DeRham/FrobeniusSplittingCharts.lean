module

public import MMP.AlgebraicGeometry.DeRham.FrobeniusSplittingMap
public import MMP.AlgebraicGeometry.DeRham.SNCCharts
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import MMP.AlgebraicGeometry.DeRham.LogFormsCriterion

/-!
# Charts with Frobenius lifts for the Deligne–Illusie decomposition

Let `V` be a smooth `k`-scheme with a simple normal crossing divisor, `𝒱` a lifting of `V` and
of the divisor over `W₂(k)`, with closed immersion `i : V → 𝒱` (the data
`MMP.DeRham.FrobeniusSplittingData`). Since `V` is the reduction of `𝒱` modulo `p`, `i` is a
homeomorphism and, on every affine open `Õ` of `𝒱`, `Γ(𝒱, Õ) → Γ(V, i⁻¹Õ)` is reduction
modulo `p`; the lifting is smooth, hence flat, over `W₂(k)`, and the components `J j` of the
divisor are the inverse images of their liftings `I j`.

A *chart with a Frobenius lift* is an affine open `𝒲` of `𝒱` with generators `tⱼ` of the
ideals of the `I j` on `𝒲` and an endomorphism `F` of `Γ(𝒱, 𝒲)` lifting the Frobenius modulo
`p` with `F tⱼ = tⱼ ^ p`. On every basic open `Õ` of `𝒲`, `F` extends to `Γ(𝒱, Õ ⊓ Ũ)`
(`Ũ` the open of `𝒱` over the complement `U` of the divisor), and `F̃^*/p` defines a
Frobenius-semilinear map `φ` on the logarithmic one-forms over `i⁻¹Õ`, with values in closed
logarithmic forms (Deligne's criterion, `MMP.DeRham.forall_exists_extension_iff_mem_logForms`).
For two charts and an open basic in both, the homotopy `η₁₂` between their maps takes values in
the functions, and `φ₂ - φ₁ = d ∘ η₁₂`, `η₁₂ + η₂₃ = η₁₃`.

## Main definitions

* `MMP.DeRham.FrobeniusSplittingData.liftOpen`: the open of `𝒱` with the points of an open of
  `V`.
* `MMP.DeRham.FrobeniusSplittingData.FrobeniusLiftChart`: a chart of the lifting with a
  Frobenius lift fixing local equations of the lifted divisor.
* `MMP.DeRham.FrobeniusSplittingData.FrobeniusLiftChart.liftOn`: the Frobenius lift on a basic
  open of a chart.
* `MMP.DeRham.FrobeniusSplittingData.FrobeniusLiftChart.phiPiece`: `φ = F̃^*/p` on the
  logarithmic one-forms over a basic open of a chart.
* `MMP.DeRham.FrobeniusSplittingData.etaPiece`: the homotopy between the maps of two charts.

## Main results

* `MMP.DeRham.FrobeniusSplittingData.isReductionModP_app`: on affine opens, the sections of the
  lifting reduce modulo `p` to those of `V`.
* `MMP.DeRham.FrobeniusSplittingData.ideal_J_eq_map`: the ideals of the divisor are the images
  of those of its lifting.
* `MMP.DeRham.FrobeniusSplittingData.mem_range_e_iff`: Deligne's criterion on a chart of the
  divisor.
* `MMP.DeRham.FrobeniusSplittingData.phiPiece_sub_phiPiece`: `φ₂ - φ₁ = d ∘ η₁₂`.
* `MMP.DeRham.FrobeniusSplittingData.etaPiece_add_etaPiece`: the cocycle relation.

## Implementation notes

The maps on a basic open `Õ` are computed on the affine open `i⁻¹Õ ⊓ U` of `V`, whose ring of
functions is the reduction modulo `p` of `Γ(𝒱, Õ ⊓ Ũ)`; on an empty piece they are zero. Every
ring and module structure attached to such a piece is stated over one affine open
(`MMP.DeRham.FrobeniusSplittingData.pieceAffine`).

## References

* [P. Deligne, L. Illusie, *Relèvements modulo p² et décomposition du complexe de de Rham*,
  Invent. Math. 89 (1987)][DeligneIllusie1987], §1–§2 and §4.2.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.Frobenius

universe u v

namespace MMP.DeRham

/-! ### Reduction modulo `p` on `W₂(k)` -/

section Witt

variable {p : ℕ} [hp : Fact p.Prime] {k : Type*} [CommRing k] [CharP k p] [PerfectRing k p]

/-- A truncated Witt vector of length two over a perfect ring with vanishing constant coefficient
is divisible by `p`. -/
theorem mem_span_natCast_of_coeff_zero_eq_zero {x : TruncatedWittVector p 2 k}
    (hx : x.coeff 0 = 0) : x ∈ Ideal.span {(p : TruncatedWittVector p 2 k)} := by
  obtain ⟨y, rfl⟩ := WittVector.truncate_surjective p 2 k x
  have hy : y.coeff 0 = 0 := by rwa [WittVector.coeff_truncate] at hx
  obtain ⟨v, hv⟩ := (WittVector.frobenius_bijective p k).2 (y.shift 1)
  have hyv : y = v * p := by
    rw [← WittVector.verschiebung_frobenius, hv]
    exact WittVector.eq_iterate_verschiebung (n := 1) fun i hi => by
      obtain rfl : i = 0 := by omega
      exact hy
  rw [hyv, map_mul, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

/-- The kernel of the reduction `W₂(k) → k` is `p W₂(k)`. -/
theorem ker_eq_span_natCast_of_coeff {π : TruncatedWittVector p 2 k →+* k}
    (hπ : ∀ x, π x = x.coeff 0) :
    RingHom.ker π = Ideal.span {(p : TruncatedWittVector p 2 k)} := by
  ext x
  refine ⟨fun hx => mem_span_natCast_of_coeff_zero_eq_zero ((hπ x).symm.trans hx), fun hx => ?_⟩
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  rw [RingHom.mem_ker, map_mul, map_natCast, CharP.cast_eq_zero, mul_zero]

omit [CharP k p] [PerfectRing k p] in
/-- The reduction `W₂(k) → k` given by the zeroth coefficient is surjective. -/
theorem surjective_of_coeff {π : TruncatedWittVector p 2 k →+* k}
    (hπ : ∀ x, π x = x.coeff 0) : Function.Surjective π :=
  fun a => ⟨TruncatedWittVector.mk p fun _ => a, by rw [hπ, TruncatedWittVector.coeff_mk]⟩

end Witt

/-- **Reduction modulo `p` composed with a bijection** is reduction modulo `p`. -/
theorem IsReductionModP.comp_bijective {p : ℕ} {R L L' : Type*} [CommRing R] [CommRing L]
    [CommRing L'] {π : R →+* L} (hπ : IsReductionModP p π) {σ : L →+* L'}
    (hσ : Function.Bijective σ) : IsReductionModP p (σ.comp π) where
  surjective := hσ.2.comp hπ.surjective
  ker_eq := by
    rw [← hπ.ker_eq]
    ext a
    simp only [RingHom.mem_ker, RingHom.comp_apply]
    exact ⟨fun h => hσ.1 (h.trans (map_zero σ).symm), fun h => by rw [h, map_zero]⟩
  mem_span_of_mul_eq_zero := hπ.mem_span_of_mul_eq_zero

/-! ### Charts of the divisor from local equations -/

section SNC

variable {k : Type u} [Field k]

private theorem mem_basicOpen_prod' {X : Scheme.{u}} {U : X.Opens} {ι : Type*} (s : Finset ι)
    (f : ι → Γ(X, U)) (y : X) :
    y ∈ X.basicOpen (∏ j ∈ s, f j) ↔ y ∈ U ∧ ∀ j ∈ s, y ∈ X.basicOpen (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Scheme.basicOpen_one, Finset.notMem_empty, IsEmpty.forall_iff,
      implies_true, and_true]
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Scheme.basicOpen_mul, TopologicalSpace.Opens.mem_inf, ih]
    simp only [Finset.mem_insert, forall_eq_or_imp]
    exact ⟨fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₂, h₁, h₃⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₂, h₁, h₃⟩⟩

/-- On an affine open `W` on which each `J j` is generated by `tⱼ`, the complement `U` of the
divisor meets `W` in the basic open `D(∏ⱼ tⱼ)`. -/
theorem inf_eq_basicOpen_prod_of_ideal_eq_span {V : Scheme.{u}} {ι : Type*} [Fintype ι]
    (J : ι → V.IdealSheafData) (U : V.Opens) (hU : U = ((⨅ j, J j).support).compl)
    (W : V.affineOpens) (t : ι → Γ(V, W)) (hideal : ∀ j, (J j).ideal W = Ideal.span {t j}) :
    (W : V.Opens) ⊓ U = V.basicOpen (∏ j, t j) := by
  refine SetLike.ext fun y ↦ ?_
  rw [TopologicalSpace.Opens.mem_inf, mem_basicOpen_prod']
  constructor
  · rintro ⟨hyW, hyU⟩
    refine ⟨hyW, fun j _ ↦ ?_⟩
    rw [hU] at hyU
    have hyU' : y ∉ (⨅ j, J j).support := hyU
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := W) hyW, Scheme.mem_zeroLocus_iff,
      Scheme.IdealSheafData.ideal_iInf, iInf_apply] at hyU'
    push Not at hyU'
    obtain ⟨a, ha, hya⟩ := hyU'
    have ha' : a ∈ (J j).ideal W := (Submodule.mem_iInf _).1 (SetLike.mem_coe.1 ha) j
    rw [hideal j, Ideal.mem_span_singleton'] at ha'
    obtain ⟨c, rfl⟩ := ha'
    rw [Scheme.basicOpen_mul] at hya
    exact hya.2
  · rintro ⟨hyW, hy⟩
    refine ⟨hyW, ?_⟩
    rw [hU]
    change y ∉ (⨅ j, J j).support
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := W) hyW, Scheme.mem_zeroLocus_iff,
      Scheme.IdealSheafData.ideal_iInf, iInf_apply]
    push Not
    refine ⟨∏ j, t j, ?_, (mem_basicOpen_prod' _ _ y).2 ⟨hyW, hy⟩⟩
    rw [SetLike.mem_coe, Submodule.mem_iInf]
    intro i
    rw [hideal i, Ideal.mem_span_singleton]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

open KaehlerDifferential TensorProduct in
/-- On an affine open `W` on which each `J j` is generated by `tⱼ`, the differentials of the
`tⱼ` lying in a prime `𝔭` are independent in `κ(𝔭) ⊗ Ω[Γ(V, W)⁄k]`, for a simple normal
crossing family `J`. -/
theorem linearIndependent_of_ideal_eq_span {V : Scheme.{u}} (f : V ⟶ Spec (.of k)) {n : ℕ}
    [SmoothOfRelativeDimension n f] {ι : Type*} [Fintype ι] (J : ι → V.IdealSheafData)
    (hJ : ∀ T : Finset ι,
      SmoothOfRelativeDimension (n - T.card) ((⨆ j ∈ T, J j).subschemeι ≫ f) ∧
      (n < T.card → IsEmpty (⨆ j ∈ T, J j).subscheme))
    (W : V.affineOpens) (t : ι → Γ(V, W)) (hideal : ∀ j, (J j).ideal W = Ideal.span {t j}) :
    letI := MMP.Mori.sectionAlgebra f W
    ∀ 𝔭 : PrimeSpectrum Γ(V, W),
      LinearIndependent 𝔭.asIdeal.ResidueField
        (fun j : {j : ι // t j ∈ 𝔭.asIdeal} ↦
          ((1 : 𝔭.asIdeal.ResidueField) ⊗ₜ[Γ(V, W)] D k Γ(V, W) (t j) :
            𝔭.asIdeal.ResidueField ⊗[Γ(V, W)] Ω[Γ(V, W)⁄k])) := by
  classical
  intro 𝔭
  set T : Finset ι := Finset.univ.filter fun j ↦ t j ∈ 𝔭.asIdeal
  set 𝒥 : V.IdealSheafData := ⨆ j ∈ T, J j
  have hcard : Fintype.card {j : ι // t j ∈ 𝔭.asIdeal} = T.card := Fintype.card_subtype _
  have hv : 𝒥.ideal W = Ideal.span (Set.range fun j : {j : ι // t j ∈ 𝔭.asIdeal} ↦ t j) := by
    have h𝒥 : 𝒥.ideal W = ⨆ j ∈ T, (J j).ideal W := by
      simp only [𝒥, Scheme.IdealSheafData.ideal_iSup, iSup_apply]
      refine iSup_congr fun i ↦ ?_
      by_cases hi : i ∈ T
      · simp only [hi, iSup_pos]
      · simp only [hi, not_false_eq_true, iSup_neg, Scheme.IdealSheafData.ideal_bot,
          Pi.bot_apply]
    rw [h𝒥]
    apply le_antisymm
    · refine iSup₂_le fun j hj ↦ ?_
      rw [hideal j]
      exact Ideal.span_mono (Set.singleton_subset_iff.2
        ⟨⟨j, (Finset.mem_filter.1 hj).2⟩, rfl⟩)
    · rw [Ideal.span_le]
      rintro _ ⟨⟨j, hj⟩, rfl⟩
      have hjT : j ∈ T := Finset.mem_filter.2 ⟨Finset.mem_univ j, hj⟩
      have : t j ∈ (J j).ideal W := by rw [hideal j]; exact Ideal.mem_span_singleton_self _
      exact (le_iSup₂ (f := fun j (_ : j ∈ T) ↦ (J j).ideal W) j hjT) this
  have h𝔭 : 𝒥.ideal W ≤ 𝔭.asIdeal := by
    rw [hv, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact j.2
  have hc : Fintype.card {j : ι // t j ∈ 𝔭.asIdeal} ≤ n := by
    by_contra hlt
    have := (hJ T).2 (by omega)
    have h1 : (1 : Γ(V, W)) ∈ 𝒥.ideal W := by
      rw [← 𝒥.ker_subschemeι_app W, RingHom.mem_ker]
      exact Subsingleton.elim _ _
    exact 𝔭.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (h𝔭 h1))
  have h𝒥s := (hJ T).1
  rw [← hcard] at h𝒥s
  exact linearIndependent_tmul_D_of_ideal_eq_span f 𝒥 W (fun j : {j : ι // t j ∈ 𝔭.asIdeal} ↦
    t j) hv hc h𝒥s 𝔭.asIdeal h𝔭

end SNC

/-! ### Frobenius lifts compatible with a reduction of a ring of functions -/

section RingLevel

open KaehlerDifferential exteriorPower

variable {p : ℕ} [hp : Fact p.Prime] (k : Type u) {A R : Type*} {B L : Type u} [CommRing A]
  [CommRing R] [CommRing B] [CommRing L] [CommRing k] [Algebra k L] [CharP L p] [ExpChar k p]
  [PerfectRing k p] [Algebra B L] {π : R →+* L} {π₀ : A →+* B} {ι : Type*} {u : ι → B}

/-- **`φ_F` preserves logarithmic forms**, for a Frobenius lift `F` on `R` compatible, along a
map `r : A → R`, with a Frobenius lift `F₀` on `A` fixing lifts `tⱼ` of the equations `uⱼ`, when
`π₀ : A → B` is surjective and `π ∘ r` is `π₀` followed by `B → L`. -/
theorem frobeniusLiftForm_mem_closedLogForms_of_map (hπ : IsReductionModP p π) {F : R →+* R}
    (hF : IsFrobeniusLift p F) (hπ₀ : Function.Surjective π₀) (r : A →+* R)
    (hr : ∀ a, π (r a) = algebraMap B L (π₀ a)) {F₀ : A →+* A} (hF₀ : IsFrobeniusLift p F₀)
    (hrF : ∀ a, F (r a) = r (F₀ a)) (t : ι → A) (ht : ∀ j, π₀ (t j) = u j)
    (hFt : ∀ j, F₀ (t j) = t j ^ p) (ω : ⋀[L]^1 (Ω[L⁄k]))
    (hω : (ω : ExteriorAlgebra L (Ω[L⁄k])) ∈ logForms k L u 1) :
    ((frobeniusLiftForm k hπ hF ω : ⋀[L]^1 (Ω[L⁄k])) : ExteriorAlgebra L (Ω[L⁄k])) ∈
      closedLogForms k L u 1 := by
  refine frobeniusLiftForm_mem_closedLogForms k hπ hF (fun b => ?_) (fun j => ?_) ω hω
  · obtain ⟨a, rfl⟩ := hπ₀ b
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hF₀ a)
    refine ⟨r a, r c, hr a, ?_, π₀ c, (hr c).symm⟩
    rw [hrF, show F₀ a = a ^ p + p * c by linear_combination -hc, map_add, map_pow, map_mul,
      map_natCast]
  · exact ⟨r (t j), by rw [hr, ht], by rw [hrF, hFt, map_pow]⟩

/-- `φ_F` transported along a linear equivalence `e : M ≃ ⋀¹ Ω[L⁄k]` is `p`-semilinear. -/
theorem conj_frobeniusLiftForm_smul (hπ : IsReductionModP p π) {F : R →+* R}
    (hF : IsFrobeniusLift p F) {M : Type*} [AddCommGroup M] [Module L M]
    (e : M ≃ₗ[L] ⋀[L]^1 (Ω[L⁄k])) (c : L) (x : M) :
    (e.symm.toAddMonoidHom.comp ((frobeniusLiftForm k hπ hF).toAddMonoidHom.comp
        e.toAddMonoidHom)) (c • x) =
      c ^ p • (e.symm.toAddMonoidHom.comp ((frobeniusLiftForm k hπ hF).toAddMonoidHom.comp
        e.toAddMonoidHom)) x := by
  simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe,
    LinearEquiv.map_smul, frobeniusLiftForm_smul]

/-- `η₁₂` transported along linear equivalences `M ≃ ⋀¹ Ω[L⁄k]`, `N ≃ ⋀⁰ Ω[L⁄k]` is
`p`-semilinear. -/
theorem conj_frobeniusLiftHomotopy_smul (hπ : IsReductionModP p π) {F₁ F₂ : R →+* R}
    (h₁ : IsFrobeniusLift p F₁) (h₂ : IsFrobeniusLift p F₂) {M N : Type*} [AddCommGroup M]
    [Module L M] [AddCommGroup N] [Module L N] (e : M ≃ₗ[L] ⋀[L]^1 (Ω[L⁄k]))
    (e' : N ≃ₗ[L] ⋀[L]^0 (Ω[L⁄k])) (c : L) (x : M) :
    (e'.symm.toAddMonoidHom.comp ((frobeniusLiftHomotopy k hπ h₁ h₂).toAddMonoidHom.comp
        e.toAddMonoidHom)) (c • x) =
      c ^ p • (e'.symm.toAddMonoidHom.comp ((frobeniusLiftHomotopy k hπ h₁ h₂).toAddMonoidHom.comp
        e.toAddMonoidHom)) x := by
  simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe,
    LinearEquiv.map_smul, frobeniusLiftHomotopy_smul]

/-- Two Frobenius lifts fixing generators `t₁`, `t₂` of the same principal ideal differ at `t₁`
by a multiple of `p t₁ ^ p`. -/
theorem exists_sub_eq_natCast_mul_pow_mul {G₁ G₂ : A →+* A}
    (h₂ : IsFrobeniusLift p G₂) {t₁ t₂ w w' : A} (hG₁ : G₁ t₁ = t₁ ^ p) (hG₂ : G₂ t₂ = t₂ ^ p)
    (hw : t₁ = w * t₂) (hw' : t₂ = w' * t₁) : ∃ c, G₂ t₁ - G₁ t₁ = p * (t₁ ^ p * c) := by
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (h₂ w)
  refine ⟨d * w' ^ p, ?_⟩
  have e0 : (w * w') ^ p * t₁ ^ p = t₁ ^ p := by
    rw [← mul_pow, mul_assoc, ← hw', ← hw]
  have e1 : G₂ t₁ = G₂ w * (w' * t₁) ^ p := by
    conv_lhs => rw [hw]
    rw [map_mul, hG₂, hw']
  rw [hG₁]
  linear_combination e1 - (w' * t₁) ^ p * hd + e0

/-- **`η₁₂` maps logarithmic forms to functions**, for Frobenius lifts `F₁, F₂` on `R` compatible,
along `r : A → R`, with Frobenius lifts `G₁, G₂` on `A` whose difference at lifts `tⱼ` of the
equations `uⱼ` is divisible by `p tⱼ ^ p`. -/
theorem frobeniusLiftHomotopy_mem_logForms_of_map (hπ : IsReductionModP p π) {F₁ F₂ : R →+* R}
    (h₁ : IsFrobeniusLift p F₁) (h₂ : IsFrobeniusLift p F₂) (hπ₀ : Function.Surjective π₀)
    (r : A →+* R) (hr : ∀ a, π (r a) = algebraMap B L (π₀ a)) {G₁ G₂ : A →+* A}
    (hG₁ : IsFrobeniusLift p G₁) (hG₂ : IsFrobeniusLift p G₂) (hrF₁ : ∀ a, F₁ (r a) = r (G₁ a))
    (hrF₂ : ∀ a, F₂ (r a) = r (G₂ a)) (t : ι → A) (ht : ∀ j, π₀ (t j) = u j)
    (hGt : ∀ j, ∃ c, G₂ (t j) - G₁ (t j) = p * (t j ^ p * c)) (ω : ⋀[L]^1 (Ω[L⁄k]))
    (hω : (ω : ExteriorAlgebra L (Ω[L⁄k])) ∈ logForms k L u 1) :
    ((frobeniusLiftHomotopy k hπ h₁ h₂ ω : ⋀[L]^0 (Ω[L⁄k])) : ExteriorAlgebra L (Ω[L⁄k])) ∈
      logForms k L u 0 := by
  refine frobeniusLiftHomotopy_mem_logForms_of_sub_eq k hπ h₁ h₂ (fun b => ?_) (fun j => ?_) ω hω
  · obtain ⟨a, rfl⟩ := hπ₀ b
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hG₁.sub_mem hG₂ a)
    refine ⟨r a, r c, hr a, ?_, π₀ c, (hr c).symm⟩
    rw [hrF₁, hrF₂, ← map_sub, ← hc, map_mul, map_natCast, mul_comm]
  · obtain ⟨c, hc⟩ := hGt j
    refine ⟨r (t j), r c, by rw [hr, ht], ?_, π₀ c, (hr c).symm⟩
    rw [hrF₁, hrF₂, ← map_sub, hc, map_mul, map_mul, map_pow, map_natCast]

end RingLevel

namespace FrobeniusSplittingData

variable {p : ℕ} [Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectField k] {n : ℕ}
  {V : Scheme.{u}} {f : V ⟶ Spec (.of k)} [IsProper f] [SmoothOfRelativeDimension n f]
  {ι : Type v} [Fintype ι] [HasDerivedCategory.{u} V.Modules]
  (D : FrobeniusSplittingData p k n f ι)

/-! ### The closed immersion of `V` in its lifting -/

/-- The reduction `π : W₂(k) → k` is surjective. -/
theorem π_surjective : Function.Surjective D.π := surjective_of_coeff D.hπ

/-- The kernel of the reduction `π : W₂(k) → k` is `p W₂(k)`. -/
theorem ker_π : RingHom.ker D.π = Ideal.span {(p : TruncatedWittVector p 2 k)} :=
  ker_eq_span_natCast_of_coeff D.hπ

/-- `Spec k → Spec W₂(k)` is a closed immersion. -/
theorem isClosedImmersion_specMap_π : IsClosedImmersion (Spec.map (CommRingCat.ofHom D.π)) :=
  IsClosedImmersion.spec_of_surjective _ D.π_surjective

/-- `i : V → 𝒱` is a closed immersion. -/
theorem isClosedImmersion_i : IsClosedImmersion D.i :=
  MorphismProperty.of_isPullback D.hi.flip D.isClosedImmersion_specMap_π

/-- `Spec k → Spec W₂(k)` is surjective. -/
theorem surjective_specMap_π : Surjective (Spec.map (CommRingCat.ofHom D.π)) := by
  refine ⟨?_⟩
  rw [Spec.map_base]
  refine (PrimeSpectrum.isHomeomorph_comap _ (fun x => ⟨1, one_pos, ?_⟩) ?_).surjective
  · obtain ⟨a, rfl⟩ := D.π_surjective x
    exact ⟨a, by rw [pow_one]; rfl⟩
  · intro x hx
    change x ∈ RingHom.ker D.π at hx
    rw [D.ker_π] at hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    refine ⟨2, ?_⟩
    rw [mul_pow, natCast_pow_eq_zero_truncatedWittVector p 2 k, mul_zero]
    exact Submodule.zero_mem _

/-- `i : V → 𝒱` is surjective. -/
theorem surjective_i : Surjective D.i :=
  MorphismProperty.of_isPullback D.hi.flip D.surjective_specMap_π

/-- `i : V → 𝒱` is an open map. -/
theorem isOpenMap_i : IsOpenMap D.i := by
  have := D.isClosedImmersion_i
  have := D.surjective_i
  exact (D.i.isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective D.i.surjective).isOpenMap

/-- The open of the lifting `𝒱` with the same points as an open `W` of `V`. -/
def liftOpen (W : V.Opens) : D.𝒱.Opens :=
  ⟨⇑D.i '' W, D.isOpenMap_i _ W.2⟩

/-- The inverse image under `i` of `liftOpen W` is `W`. -/
theorem preimage_liftOpen (W : V.Opens) : D.i ⁻¹ᵁ D.liftOpen W = W := by
  have := D.isClosedImmersion_i
  ext x
  change D.i x ∈ ⇑D.i '' W ↔ x ∈ W
  exact D.i.isClosedEmbedding.injective.mem_set_image

/-- Inverse images under `i` of opens of `𝒱` compare as the opens do. -/
theorem preimage_le_preimage_iff {A B : D.𝒱.Opens} : D.i ⁻¹ᵁ A ≤ D.i ⁻¹ᵁ B ↔ A ≤ B := by
  have := D.surjective_i
  refine ⟨fun h y hy => ?_, D.i.preimage_mono⟩
  obtain ⟨x, rfl⟩ := D.i.surjective y
  exact h hy

/-- Taking the inverse image under `i` is injective on the opens of `𝒱`. -/
theorem preimage_injective : Function.Injective (fun A : D.𝒱.Opens => D.i ⁻¹ᵁ A) :=
  fun _ _ h => le_antisymm (D.preimage_le_preimage_iff.1 h.le) (D.preimage_le_preimage_iff.1 h.ge)

/-! ### Sections of the lifting -/

/-- The structure map `W₂(k) → Γ(𝒱, Õ)` of the lifting. -/
def sectionsRingHom (Õ : D.𝒱.Opens) : TruncatedWittVector p 2 k →+* Γ(D.𝒱, Õ) :=
  (D.g.appLE ⊤ Õ fun _ _ => trivial).hom.comp
    (Scheme.ΓSpecIso (.of (TruncatedWittVector p 2 k))).inv.hom

/-- `p ^ 2 = 0` in the sections of the lifting. -/
theorem natCast_sq_eq_zero (Õ : D.𝒱.Opens) : (p : Γ(D.𝒱, Õ)) ^ 2 = 0 := by
  rw [← map_natCast (D.sectionsRingHom Õ), ← map_pow, natCast_pow_eq_zero_truncatedWittVector,
    map_zero]

/-- The lifting is smooth over `W₂(k)`. -/
theorem smooth_g : Smooth D.g := by
  have h := (D.hI ∅).1
  have hbot : (⨆ j ∈ (∅ : Finset ι), D.I j) = ⊥ := by simp
  have : IsIso (⨆ j ∈ (∅ : Finset ι), D.I j).subschemeι :=
    (Scheme.isIso_subschemeι_iff_eq_bot _).2 hbot
  have : Smooth ((⨆ j ∈ (∅ : Finset ι), D.I j).subschemeι ≫ D.g) :=
    SmoothOfRelativeDimension.smooth (n - (∅ : Finset ι).card) _
  rw [← IsIso.inv_hom_id_assoc (⨆ j ∈ (∅ : Finset ι), D.I j).subschemeι D.g]
  infer_instance

/-- The sections of the lifting over an affine open are flat over `W₂(k)`. -/
theorem flat_sectionsRingHom (Õ : D.𝒱.Opens) (hÕ : IsAffineOpen Õ) :
    (D.sectionsRingHom Õ).Flat :=
  RingHom.Flat.comp (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv))
    (HasRingHomProperty.appLE @AlgebraicGeometry.Smooth D.g D.smooth_g ⟨⊤, isAffineOpen_top _⟩
      ⟨Õ, hÕ⟩ _).flat

/-- Over an affine open, a section of the lifting killed by `p` is divisible by `p`. -/
theorem mem_span_of_natCast_mul_eq_zero (Õ : D.𝒱.Opens) (hÕ : IsAffineOpen Õ) (a : Γ(D.𝒱, Õ))
    (ha : (p : Γ(D.𝒱, Õ)) * a = 0) : a ∈ Ideal.span {(p : Γ(D.𝒱, Õ))} := by
  let := (D.sectionsRingHom Õ).toAlgebra
  have : Module.Flat (TruncatedWittVector p 2 k) Γ(D.𝒱, Õ) := D.flat_sectionsRingHom Õ hÕ
  exact mem_span_natCast_of_natCast_mul_eq_zero_of_flat p k ha

/-- The kernel of `Spec k → Spec W₂(k)` on global sections is generated by `p`. -/
theorem ker_specMap_π_app_top :
    RingHom.ker ((Spec.map (CommRingCat.ofHom D.π)).app ⊤).hom =
      Ideal.span {(p : Γ(Spec (.of (TruncatedWittVector p 2 k)), ⊤))} := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom D.π)
  set e := Scheme.ΓSpecIso (CommRingCat.of (TruncatedWittVector p 2 k))
  set e' := Scheme.ΓSpecIso (CommRingCat.of k)
  have hx : ∀ x, e'.hom ((Spec.map (CommRingCat.ofHom D.π)).app ⊤ x) = D.π (e.hom x) :=
    fun x => congr(($h).hom x)
  have he' : Function.Injective e'.hom := (ConcreteCategory.bijective_of_isIso e'.hom).1
  ext x
  rw [RingHom.mem_ker]
  constructor
  · intro h0
    have hmem : e.hom x ∈ RingHom.ker D.π := by
      rw [RingHom.mem_ker, ← hx]
      exact (congrArg e'.hom h0).trans (map_zero _)
    rw [D.ker_π] at hmem
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
    refine Ideal.mem_span_singleton'.2 ⟨e.inv c, (ConcreteCategory.bijective_of_isIso e.hom).1 ?_⟩
    change e.hom (e.inv c * p) = e.hom x
    rw [map_mul, map_natCast, ← hc, Iso.inv_hom_id_apply]
  · intro hx'
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx'
    have hp0' : (p : Γ(Spec (.of k), ⊤)) = 0 :=
      he' (by rw [map_natCast, map_zero]; exact CharP.cast_eq_zero k p)
    have hp0 : (p : Γ(Spec (.of k), Spec.map (CommRingCat.ofHom D.π) ⁻¹ᵁ ⊤)) = 0 := hp0'
    rw [map_mul, map_natCast, hp0, mul_zero]

/-- The kernel of the reduction `Γ(𝒱, Õ) → Γ(V, i⁻¹Õ)` is `p Γ(𝒱, Õ)`. -/
theorem ker_app_i (Õ : D.𝒱.Opens) (hÕ : IsAffineOpen Õ) :
    RingHom.ker (D.i.app Õ).hom = Ideal.span {(p : Γ(D.𝒱, Õ))} := by
  have := D.isClosedImmersion_i
  have := D.isClosedImmersion_specMap_π
  have hker : D.i.ker = (Spec.map (CommRingCat.ofHom D.π)).ker.comap D.g := by
    rw [← D.hi.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
      Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  rw [← Scheme.Hom.ker_apply D.i ⟨Õ, hÕ⟩, hker,
    Stacks.IdealSheaf.ideal_comap_appLE _ D.g ⟨⊤, isAffineOpen_top _⟩ ⟨Õ, hÕ⟩ fun _ _ => trivial,
    Scheme.Hom.ker_apply _ ⟨⊤, isAffineOpen_top _⟩]
  change Ideal.map _ (RingHom.ker ((Spec.map (CommRingCat.ofHom D.π)).app ⊤).hom) = _
  rw [D.ker_specMap_π_app_top, Ideal.map_span, Set.image_singleton, map_natCast]

/-- **On affine opens, `Γ(𝒱, Õ) → Γ(V, i⁻¹Õ)` is reduction modulo `p`.** -/
theorem isReductionModP_app (Õ : D.𝒱.Opens) (hÕ : IsAffineOpen Õ) :
    IsReductionModP p (D.i.app Õ).hom where
  surjective := haveI := D.isClosedImmersion_i; D.i.app_surjective Õ hÕ
  ker_eq := D.ker_app_i Õ hÕ
  mem_span_of_mul_eq_zero := D.mem_span_of_natCast_mul_eq_zero Õ hÕ

/-- The inverse image under `i` of an affine open of `𝒱` is affine. -/
theorem isAffineOpen_preimage {Õ : D.𝒱.Opens} (hÕ : IsAffineOpen Õ) :
    IsAffineOpen (D.i ⁻¹ᵁ Õ) :=
  haveI := D.isClosedImmersion_i
  hÕ.preimage D.i

/-- The components of the divisor are the inverse images of their liftings. -/
theorem J_eq_comap (j : ι) : D.J j = (D.I j).comap D.i := by
  have := D.isClosedImmersion_i
  obtain ⟨φ, hφ⟩ := D.hIJ j
  rw [← (D.J j).ker_subschemeι, ← hφ.flip.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, Scheme.IdealSheafData.ker_subschemeι]

/-- On an affine open `Õ` of `𝒱`, the ideal of `J j` on `i⁻¹Õ` is the image of the ideal of `I j`
on `Õ`. -/
theorem ideal_J_eq_map (j : ι) {Õ : D.𝒱.Opens} (hÕ : IsAffineOpen Õ) :
    (D.J j).ideal ⟨D.i ⁻¹ᵁ Õ, D.isAffineOpen_preimage hÕ⟩ =
      ((D.I j).ideal ⟨Õ, hÕ⟩).map (D.i.app Õ).hom := by
  rw [D.J_eq_comap j]
  exact (Stacks.IdealSheaf.ideal_comap_appLE (D.I j) D.i ⟨Õ, hÕ⟩
    ⟨D.i ⁻¹ᵁ Õ, D.isAffineOpen_preimage hÕ⟩ le_rfl).trans (by simp [Scheme.Hom.app_eq_appLE])

/-! ### Charts with a Frobenius lift -/

/-- Restricting a section of the structure sheaf twice is restricting it once. -/
theorem structureSheaf_map_map {X : Scheme.{u}} {A B C : X.Opens} (h₁ : B ≤ A) (h₂ : C ≤ B)
    (a : Γ(X, A)) :
    X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op a) =
      X.presheaf.map (homOfLE (h₂.trans h₁)).op a :=
  TopCat.Presheaf.restrict_restrict (F := X.presheaf) h₂ h₁ a

/-- **A chart of the lifting with a Frobenius lift**: an affine open `𝒲` of `𝒱`, generators `tⱼ`
of the ideals of the lifted components `I j` on `𝒲`, and a ring endomorphism `F` of `Γ(𝒱, 𝒲)`
lifting the Frobenius modulo `p` with `F tⱼ = tⱼ ^ p`. -/
structure FrobeniusLiftChart where
  /-- The affine open of the lifting. -/
  𝒲 : D.𝒱.Opens
  isAffineOpen : IsAffineOpen 𝒲
  /-- The local equations of the lifted divisor. -/
  t : ι → Γ(D.𝒱, 𝒲)
  ideal_eq : ∀ j, (D.I j).ideal ⟨𝒲, isAffineOpen⟩ = Ideal.span {t j}
  /-- The Frobenius lift. -/
  F : Γ(D.𝒱, 𝒲) →+* Γ(D.𝒱, 𝒲)
  isFrobeniusLift : IsFrobeniusLift p F
  F_t : ∀ j, F (t j) = t j ^ p

namespace FrobeniusLiftChart

variable {D} (C : D.FrobeniusLiftChart)

/-- An open of the lifting is a basic open of the chart. -/
def IsBasic (Õ : D.𝒱.Opens) : Prop :=
  ∃ a : Γ(D.𝒱, C.𝒲), D.𝒱.basicOpen a = Õ

variable {C}

/-- A basic open of a chart is contained in the chart. -/
theorem IsBasic.le {Õ : D.𝒱.Opens} (h : C.IsBasic Õ) : Õ ≤ C.𝒲 := by
  obtain ⟨a, rfl⟩ := h
  exact D.𝒱.basicOpen_le a

/-- A basic open of a chart is affine. -/
theorem IsBasic.isAffineOpen {Õ : D.𝒱.Opens} (h : C.IsBasic Õ) : IsAffineOpen Õ := by
  obtain ⟨a, rfl⟩ := h
  exact C.isAffineOpen.basicOpen a

/-- The intersection of two basic opens of a chart is a basic open of the chart. -/
theorem IsBasic.inf {Õ Õ' : D.𝒱.Opens} (h : C.IsBasic Õ) (h' : C.IsBasic Õ') :
    C.IsBasic (Õ ⊓ Õ') := by
  obtain ⟨a, rfl⟩ := h
  obtain ⟨b, rfl⟩ := h'
  exact ⟨a * b, D.𝒱.basicOpen_mul a b⟩

/-- A basic open of a basic open of a chart is a basic open of the chart. -/
theorem isBasic_basicOpen {Õ : D.𝒱.Opens} (h : C.IsBasic Õ) (b : Γ(D.𝒱, Õ)) :
    C.IsBasic (D.𝒱.basicOpen b) := by
  obtain ⟨a, rfl⟩ := h
  obtain ⟨c, hc⟩ := C.isAffineOpen.basicOpen_basicOpen_is_basicOpen a b
  exact ⟨c, hc⟩

/-- The sections over a basic open `D(a)` of a chart are the localization away from `a` of the
sections over the chart. -/
theorem IsBasic.isLocalization {Õ : D.𝒱.Opens} (h : C.IsBasic Õ) :
    letI : Algebra Γ(D.𝒱, C.𝒲) Γ(D.𝒱, Õ) := (D.𝒱.presheaf.map (homOfLE h.le).op).hom.toAlgebra
    IsLocalization.Away h.choose Γ(D.𝒱, Õ) :=
  C.isAffineOpen.isLocalization_of_eq_basicOpen _ (homOfLE h.le) h.choose_spec.symm

variable (C)

/-- On a basic open of a chart, `F` extends to a Frobenius lift compatible with restriction from
the chart. -/
theorem exists_liftOn {Õ : D.𝒱.Opens} (h : C.IsBasic Õ) :
    ∃ F' : Γ(D.𝒱, Õ) →+* Γ(D.𝒱, Õ), IsFrobeniusLift p F' ∧
      ∀ a, F' (D.𝒱.presheaf.map (homOfLE h.le).op a) =
        D.𝒱.presheaf.map (homOfLE h.le).op (C.F a) := by
  let : Algebra Γ(D.𝒱, C.𝒲) Γ(D.𝒱, Õ) := (D.𝒱.presheaf.map (homOfLE h.le).op).hom.toAlgebra
  have := h.isLocalization
  exact exists_isFrobeniusLift_isLocalization_away_of_isNilpotent h.choose
    ⟨2, D.natCast_sq_eq_zero _⟩ C.isFrobeniusLift

/-- **The Frobenius lift of a chart on a basic open**, the extension of `F` to the
localization. -/
def liftOn {Õ : D.𝒱.Opens} (h : C.IsBasic Õ) : Γ(D.𝒱, Õ) →+* Γ(D.𝒱, Õ) :=
  (C.exists_liftOn h).choose

/-- `liftOn` is a Frobenius lift. -/
theorem isFrobeniusLift_liftOn {Õ : D.𝒱.Opens} (h : C.IsBasic Õ) :
    IsFrobeniusLift p (C.liftOn h) :=
  (C.exists_liftOn h).choose_spec.1

/-- `liftOn` extends `F` along restriction from the chart. -/
theorem liftOn_map {Õ : D.𝒱.Opens} (h : C.IsBasic Õ) (a : Γ(D.𝒱, C.𝒲)) :
    C.liftOn h (D.𝒱.presheaf.map (homOfLE h.le).op a) =
      D.𝒱.presheaf.map (homOfLE h.le).op (C.F a) :=
  (C.exists_liftOn h).choose_spec.2 a

/-- The Frobenius lifts on basic opens are compatible with restriction. -/
theorem liftOn_map_of_le {Õ Õ' : D.𝒱.Opens} (h : C.IsBasic Õ) (h' : C.IsBasic Õ')
    (hle : Õ' ≤ Õ) (a : Γ(D.𝒱, Õ)) :
    C.liftOn h' (D.𝒱.presheaf.map (homOfLE hle).op a) =
      D.𝒱.presheaf.map (homOfLE hle).op (C.liftOn h a) := by
  let : Algebra Γ(D.𝒱, C.𝒲) Γ(D.𝒱, Õ) := (D.𝒱.presheaf.map (homOfLE h.le).op).hom.toAlgebra
  have := h.isLocalization
  have key : ((C.liftOn h').comp (D.𝒱.presheaf.map (homOfLE hle).op).hom).comp
      (algebraMap Γ(D.𝒱, C.𝒲) Γ(D.𝒱, Õ)) =
      (((D.𝒱.presheaf.map (homOfLE hle).op).hom).comp (C.liftOn h)).comp
        (algebraMap Γ(D.𝒱, C.𝒲) Γ(D.𝒱, Õ)) := by
    ext b
    simp only [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
    change C.liftOn h' (D.𝒱.presheaf.map (homOfLE hle).op
        (D.𝒱.presheaf.map (homOfLE h.le).op b)) =
      D.𝒱.presheaf.map (homOfLE hle).op (C.liftOn h (D.𝒱.presheaf.map (homOfLE h.le).op b))
    rw [structureSheaf_map_map, C.liftOn_map h', C.liftOn_map h, structureSheaf_map_map]
  exact RingHom.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers h.choose) key) a

/-- `liftOn` sends the restriction of `tⱼ` to its `p`-th power. -/
theorem liftOn_t {Õ : D.𝒱.Opens} (h : C.IsBasic Õ) (j : ι) :
    C.liftOn h (D.𝒱.presheaf.map (homOfLE h.le).op (C.t j)) =
      D.𝒱.presheaf.map (homOfLE h.le).op (C.t j) ^ p := by
  rw [C.liftOn_map, C.F_t, map_pow]

end FrobeniusLiftChart

/-! ### The pieces of a chart -/

include D in
/-- A nontrivial ring of sections of `V` has characteristic `p`. -/
theorem charP_of_nontrivial (A : V.Opens) [Nontrivial Γ(V, A)] : CharP Γ(V, A) p :=
  (CharP.charP_iff_prime_eq_zero Fact.out).2 (cast_eq_zero_of_isInCharacteristic D.hV _)

include D in
/-- If the sections over `B ≤ A` form a nontrivial ring, so do the sections over `A`. -/
theorem nontrivial_of_le {A B : V.Opens} (h : B ≤ A) [Nontrivial Γ(V, B)] :
    Nontrivial Γ(V, A) :=
  (V.presheaf.map (homOfLE h).op).hom.domain_nontrivial

/-- **Deligne's criterion on a chart** of the divisor: a form on `W ∩ U` has logarithmic poles in
the sense of `he_range` exactly when, read in `⋀ Ω[Γ(V, W ∩ U)⁄k]`, it lies in `logForms`. -/
theorem mem_range_e_iff (W : V.affineOpens) (t : ι → Γ(V, W))
    (hideal : ∀ j, (D.J j).ideal W = Ideal.span {t j}) (q : ℕ)
    (ω : Γ(f.relativeDifferentialForms (q : ℤ), (W : V.Opens) ⊓ D.U)) :
    ω ∈ Set.range (D.e q W) ↔
      letI := MMP.Mori.sectionAlgebra f W
      letI := MMP.Mori.sectionAlgebra f ((W : V.Opens) ⊓ D.U)
      letI : Algebra Γ(V, W) Γ(V, (W : V.Opens) ⊓ D.U) :=
        (V.presheaf.map (homOfLE (inf_le_left : (W : V.Opens) ⊓ D.U ≤ W)).op).hom.toAlgebra
      ((formsAlgEquiv f q ⟨(W : V.Opens) ⊓ D.U, isAffineOpen_of_eq_basicOpen _
          (inf_eq_basicOpen_prod_of_ideal_eq_span D.J D.U D.hU W t hideal)⟩ ω :
          ⋀[Γ(V, (W : V.Opens) ⊓ D.U)]^q (Ω[Γ(V, (W : V.Opens) ⊓ D.U)⁄k])) :
        ExteriorAlgebra Γ(V, (W : V.Opens) ⊓ D.U) (Ω[Γ(V, (W : V.Opens) ⊓ D.U)⁄k])) ∈
        logForms k Γ(V, (W : V.Opens) ⊓ D.U) t q := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  exact (D.he_range q W ω).trans (forall_exists_extension_iff_mem_logForms f W D.J t hideal D.U
    (inf_eq_basicOpen_prod_of_ideal_eq_span D.J D.U D.hU W t hideal)
    (linearIndependent_of_ideal_eq_span f D.J D.hJ W t hideal) q ω)

/-- The inverse image under `i` of `Õ ⊓ Ũ` is `i⁻¹Õ ⊓ U`. -/
theorem preimage_inf_liftOpen (Õ : D.𝒱.Opens) :
    D.i ⁻¹ᵁ (Õ ⊓ D.liftOpen D.U) = D.i ⁻¹ᵁ Õ ⊓ D.U := by
  rw [Scheme.Hom.preimage_inf, D.preimage_liftOpen]

/-- Restriction of sections between equal opens is bijective. -/
theorem bijective_structureSheaf_map_of_eq {X : Scheme.{u}} {A B : X.Opens} (h : B = A) :
    Function.Bijective (X.presheaf.map (homOfLE h.le).op).hom := by
  refine Function.bijective_iff_has_inverse.2 ⟨(X.presheaf.map (homOfLE h.ge).op).hom,
    fun a => ?_, fun a => ?_⟩ <;>
  · change X.presheaf.map _ (X.presheaf.map _ a) = a
    rw [structureSheaf_map_map, show (homOfLE _).op = 𝟙 _ from rfl, X.presheaf.map_id]
    rfl

/-- The reduction `Γ(𝒱, Õ ⊓ Ũ) → Γ(V, i⁻¹Õ ⊓ U)` on the complement of the divisor. -/
def pieceReduction (Õ : D.𝒱.Opens) :
    Γ(D.𝒱, Õ ⊓ D.liftOpen D.U) →+* Γ(V, D.i ⁻¹ᵁ Õ ⊓ D.U) :=
  (D.i.appLE _ _ (D.preimage_inf_liftOpen Õ).ge).hom

/-- `pieceReduction` is `i.app (Õ ⊓ Ũ)` followed by the identification of `i⁻¹(Õ ⊓ Ũ)` with
`i⁻¹Õ ⊓ U`. -/
theorem pieceReduction_eq (Õ : D.𝒱.Opens) :
    D.pieceReduction Õ = (V.presheaf.map (homOfLE (D.preimage_inf_liftOpen Õ).ge).op).hom.comp
      (D.i.app (Õ ⊓ D.liftOpen D.U)).hom := by
  rw [pieceReduction, Scheme.Hom.app_eq_appLE, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]

/-- The reduction of the restriction to `Õ ⊓ Ũ` of a section over `Õ` is the restriction of its
image under `i`. -/
theorem pieceReduction_map_app (Õ : D.𝒱.Opens) (a : Γ(D.𝒱, Õ)) :
    D.pieceReduction Õ (D.𝒱.presheaf.map (homOfLE inf_le_left).op a) =
      V.presheaf.map (homOfLE (inf_le_left : D.i ⁻¹ᵁ Õ ⊓ D.U ≤ D.i ⁻¹ᵁ Õ)).op
        ((D.i.app Õ).hom a) := by
  change (D.𝒱.presheaf.map _ ≫ D.i.appLE _ _ _) a = (D.i.app Õ ≫ V.presheaf.map _) a
  rw [Scheme.Hom.map_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]

/-- The affine open `i⁻¹Õ ⊓ U` of `V`. -/
abbrev pieceAffine (Õ : D.𝒱.Opens) (hA : IsAffineOpen (D.i ⁻¹ᵁ Õ ⊓ D.U)) : V.affineOpens :=
  ⟨_, hA⟩

/-- The reduction on a piece, with values in the sections over `pieceAffine`. -/
abbrev pieceReductionAt (Õ : D.𝒱.Opens) (hA : IsAffineOpen (D.i ⁻¹ᵁ Õ ⊓ D.U)) :
    Γ(D.𝒱, Õ ⊓ D.liftOpen D.U) →+* Γ(V, D.pieceAffine Õ hA) :=
  D.pieceReduction Õ

/-- When `Õ ⊓ Ũ` is affine, `pieceReductionAt` is reduction modulo `p`. -/
theorem isReductionModP_pieceReductionAt (Õ : D.𝒱.Opens) (hA : IsAffineOpen (D.i ⁻¹ᵁ Õ ⊓ D.U))
    (h : IsAffineOpen (Õ ⊓ D.liftOpen D.U)) : IsReductionModP p (D.pieceReductionAt Õ hA) := by
  rw [pieceReductionAt, D.pieceReduction_eq]
  exact (D.isReductionModP_app _ h).comp_bijective
    (bijective_structureSheaf_map_of_eq (D.preimage_inf_liftOpen Õ).symm)

/-- The affine open `i⁻¹Õ ⊓ U` is monotone in `Õ`. -/
theorem pieceAffine_le {Õ Õ' : D.𝒱.Opens} (hle : Õ' ≤ Õ) (hA : IsAffineOpen (D.i ⁻¹ᵁ Õ ⊓ D.U))
    (hA' : IsAffineOpen (D.i ⁻¹ᵁ Õ' ⊓ D.U)) :
    (D.pieceAffine Õ' hA' : V.Opens) ≤ D.pieceAffine Õ hA :=
  inf_le_inf_right D.U (D.i.preimage_mono hle)

/-- The reductions `pieceReductionAt` are compatible with restriction. -/
theorem pieceReductionAt_map {Õ Õ' : D.𝒱.Opens} (hle : Õ' ≤ Õ)
    (hA : IsAffineOpen (D.i ⁻¹ᵁ Õ ⊓ D.U)) (hA' : IsAffineOpen (D.i ⁻¹ᵁ Õ' ⊓ D.U))
    (a : Γ(D.𝒱, Õ ⊓ D.liftOpen D.U)) :
    D.pieceReductionAt Õ' hA' (D.𝒱.presheaf.map (homOfLE (inf_le_inf_right _ hle)).op a) =
      V.presheaf.map (homOfLE (D.pieceAffine_le hle hA hA')).op (D.pieceReductionAt Õ hA a) := by
  change (D.𝒱.presheaf.map _ ≫ D.i.appLE _ _ _) a = (D.i.appLE _ _ _ ≫ V.presheaf.map _) a
  rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

/-- Forms over an open whose ring of sections is trivial are all equal. -/
theorem relativeDifferentialForms_eq_of_not_nontrivial {A : V.Opens} {q : ℤ}
    (h : ¬ Nontrivial Γ(V, A)) (a b : Γ(f.relativeDifferentialForms q, A)) : a = b :=
  haveI := not_nontrivial_iff_subsingleton.1 h
  (Module.subsingleton Γ(V, A) Γ(f.relativeDifferentialForms q, A)).elim a b

namespace FrobeniusLiftChart

variable {D} (C : D.FrobeniusLiftChart)

/-- The reductions of the local equations of the divisor on the inverse image of an open of the
chart. -/
def u {Õ : D.𝒱.Opens} (h : Õ ≤ C.𝒲) (j : ι) : Γ(V, D.i ⁻¹ᵁ Õ) :=
  (D.i.app Õ).hom (D.𝒱.presheaf.map (homOfLE h).op (C.t j))

/-- On the inverse image of a basic open of a chart, the ideal of `J j` is generated by `u j`. -/
theorem ideal_J_eq_span_u {Õ : D.𝒱.Opens} (h : C.IsBasic Õ) (j : ι) :
    (D.J j).ideal ⟨D.i ⁻¹ᵁ Õ, D.isAffineOpen_preimage h.isAffineOpen⟩ =
      Ideal.span {C.u h.le j} := by
  rw [D.ideal_J_eq_map j h.isAffineOpen]
  have := (D.I j).map_ideal (U := ⟨Õ, h.isAffineOpen⟩) (V := ⟨C.𝒲, C.isAffineOpen⟩) h.le
  rw [← this, C.ideal_eq, Ideal.map_span, Set.image_singleton, Ideal.map_span,
    Set.image_singleton]
  rfl

/-- A chart meets `Ũ` in the basic open `D(∏ⱼ tⱼ)`. -/
theorem inf_liftOpen_eq : C.𝒲 ⊓ D.liftOpen D.U = D.𝒱.basicOpen (∏ j, C.t j) := by
  refine D.preimage_injective ?_
  change D.i ⁻¹ᵁ (C.𝒲 ⊓ D.liftOpen D.U) = D.i ⁻¹ᵁ D.𝒱.basicOpen (∏ j, C.t j)
  rw [D.preimage_inf_liftOpen, Scheme.preimage_basicOpen, map_prod]
  refine inf_eq_basicOpen_prod_of_ideal_eq_span D.J D.U D.hU
    ⟨_, D.isAffineOpen_preimage C.isAffineOpen⟩ _ fun j => ?_
  rw [D.ideal_J_eq_map j C.isAffineOpen, C.ideal_eq, Ideal.map_span, Set.image_singleton]

variable {C}

/-- The intersection of a basic open of a chart with `Ũ` is a basic open of the chart. -/
theorem IsBasic.inf_U {Õ : D.𝒱.Opens} (h : C.IsBasic Õ) : C.IsBasic (Õ ⊓ D.liftOpen D.U) := by
  have : Õ ⊓ D.liftOpen D.U = Õ ⊓ D.𝒱.basicOpen (∏ j, C.t j) := by
    rw [← C.inf_liftOpen_eq, ← inf_assoc, inf_eq_left.2 h.le]
  rw [this]
  exact h.inf ⟨_, rfl⟩

/-- For a basic open `Õ` of a chart, `i⁻¹Õ ⊓ U` is affine. -/
theorem IsBasic.isAffineOpen_inf_U {Õ : D.𝒱.Opens} (h : C.IsBasic Õ) :
    IsAffineOpen (D.i ⁻¹ᵁ Õ ⊓ D.U) :=
  D.preimage_inf_liftOpen Õ ▸ D.isAffineOpen_preimage h.inf_U.isAffineOpen

variable (C)

open scoped Classical in
/-- **The local Frobenius form `φ = F̃^*/p` on a piece** `i⁻¹Õ ⊓ U` of a chart, read on the
sections of `Ω¹` (zero when the piece is empty). -/
def frobeniusForm {Õ : D.𝒱.Opens} (h : C.IsBasic Õ) :
    Γ(f.relativeDifferentialForms ((1 : ℕ) : ℤ), D.pieceAffine Õ h.isAffineOpen_inf_U) →+
      Γ(f.relativeDifferentialForms ((1 : ℕ) : ℤ), D.pieceAffine Õ h.isAffineOpen_inf_U) :=
  letI := MMP.Mori.sectionAlgebra f (D.pieceAffine Õ h.isAffineOpen_inf_U)
  if hL : Nontrivial Γ(V, D.pieceAffine Õ h.isAffineOpen_inf_U) then
    haveI := charP_of_nontrivial D (D.pieceAffine Õ h.isAffineOpen_inf_U)
    (formsAlgEquiv f 1 (D.pieceAffine Õ h.isAffineOpen_inf_U)).symm.toAddMonoidHom.comp
      ((frobeniusLiftForm k (D.isReductionModP_pieceReductionAt Õ h.isAffineOpen_inf_U
          h.inf_U.isAffineOpen) (C.isFrobeniusLift_liftOn h.inf_U)).toAddMonoidHom.comp
        (formsAlgEquiv f 1 (D.pieceAffine Õ h.isAffineOpen_inf_U)).toAddMonoidHom)
  else 0

/-- On a piece with nontrivial ring of functions, `frobeniusForm` read in `⋀¹ Ω` is
`frobeniusLiftForm` of the Frobenius lift `liftOn`. -/
theorem formsAlgEquiv_frobeniusForm {Õ : D.𝒱.Opens} (h : C.IsBasic Õ)
    [hL : Nontrivial Γ(V, D.pieceAffine Õ h.isAffineOpen_inf_U)]
    (ω : Γ(f.relativeDifferentialForms ((1 : ℕ) : ℤ), D.pieceAffine Õ h.isAffineOpen_inf_U)) :
    letI := MMP.Mori.sectionAlgebra f (D.pieceAffine Õ h.isAffineOpen_inf_U)
    haveI := charP_of_nontrivial D (D.pieceAffine Õ h.isAffineOpen_inf_U)
    formsAlgEquiv f 1 (D.pieceAffine Õ h.isAffineOpen_inf_U) (C.frobeniusForm h ω) =
      frobeniusLiftForm k (D.isReductionModP_pieceReductionAt Õ h.isAffineOpen_inf_U
          h.inf_U.isAffineOpen) (C.isFrobeniusLift_liftOn h.inf_U)
        (formsAlgEquiv f 1 (D.pieceAffine Õ h.isAffineOpen_inf_U) ω) := by
  classical
  rw [frobeniusForm, dite_eq_left hL]
  simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

/-- `frobeniusForm` is `p`-semilinear. -/
theorem frobeniusForm_smul {Õ : D.𝒱.Opens} (h : C.IsBasic Õ)
    (c : Γ(V, D.pieceAffine Õ h.isAffineOpen_inf_U))
    (ω : Γ(f.relativeDifferentialForms ((1 : ℕ) : ℤ), D.pieceAffine Õ h.isAffineOpen_inf_U)) :
    C.frobeniusForm h (c • ω) = c ^ p • C.frobeniusForm h ω := by
  classical
  by_cases hL : Nontrivial Γ(V, D.pieceAffine Õ h.isAffineOpen_inf_U)
  · let := MMP.Mori.sectionAlgebra f (D.pieceAffine Õ h.isAffineOpen_inf_U)
    have := charP_of_nontrivial D (D.pieceAffine Õ h.isAffineOpen_inf_U)
    rw [frobeniusForm, dite_eq_left hL]
    have := conj_frobeniusLiftForm_smul k
      (D.isReductionModP_pieceReductionAt Õ h.isAffineOpen_inf_U h.inf_U.isAffineOpen)
      (C.isFrobeniusLift_liftOn h.inf_U) (formsAlgEquiv f 1 (D.pieceAffine Õ h.isAffineOpen_inf_U))
      c ω
    convert this using 1
  · exact relativeDifferentialForms_eq_of_not_nontrivial hL _ _

/-- The local Frobenius form of the form of a section of `K¹` over `i⁻¹Õ` is the form of a section
of `K¹` over `i⁻¹Õ`. -/
theorem frobeniusForm_mem_range {Õ : D.𝒱.Opens} (h : C.IsBasic Õ) (s : Γ(D.K 1, D.i ⁻¹ᵁ Õ)) :
    C.frobeniusForm h (D.e 1 _ s) ∈ Set.range (D.e 1 (D.i ⁻¹ᵁ Õ)) := by
  classical
  set P := D.pieceAffine Õ h.isAffineOpen_inf_U
  by_cases hL : Nontrivial Γ(V, P)
  swap
  · rw [frobeniusForm, dite_eq_right hL]
    exact ⟨0, map_zero _⟩
  have hcrit := D.mem_range_e_iff ⟨D.i ⁻¹ᵁ Õ, D.isAffineOpen_preimage h.isAffineOpen⟩
    (C.u h.le) (C.ideal_J_eq_span_u h) 1
  have hs := (hcrit (D.e 1 _ s)).1 ⟨s, rfl⟩
  let := MMP.Mori.sectionAlgebra f P
  let : Algebra Γ(V, D.i ⁻¹ᵁ Õ) Γ(V, P) :=
    (V.presheaf.map (homOfLE (inf_le_left : D.i ⁻¹ᵁ Õ ⊓ D.U ≤ D.i ⁻¹ᵁ Õ)).op).hom.toAlgebra
  have := charP_of_nontrivial D P
  have key : ((formsAlgEquiv f 1 P (C.frobeniusForm h (D.e 1 _ s)) :
      ⋀[Γ(V, P)]^1 (Ω[Γ(V, P)⁄k])) : ExteriorAlgebra Γ(V, P) (Ω[Γ(V, P)⁄k])) ∈
      logForms k Γ(V, P) (C.u h.le) 1 := by
    rw [C.formsAlgEquiv_frobeniusForm h]
    have := (frobeniusLiftForm_mem_closedLogForms_of_map k (u := C.u h.le)
      (D.isReductionModP_pieceReductionAt Õ h.isAffineOpen_inf_U h.inf_U.isAffineOpen)
      (C.isFrobeniusLift_liftOn h.inf_U) (D.isReductionModP_app Õ h.isAffineOpen).surjective
      (D.𝒱.presheaf.map (homOfLE (inf_le_left : Õ ⊓ D.liftOpen D.U ≤ Õ)).op).hom
      (D.pieceReduction_map_app Õ) (C.isFrobeniusLift_liftOn h)
      (C.liftOn_map_of_le h h.inf_U inf_le_left)
      (fun j => D.𝒱.presheaf.map (homOfLE h.le).op (C.t j)) (fun _ => rfl) (C.liftOn_t h)
      (formsAlgEquiv f 1 P (D.e 1 _ s)) (by convert hs using 3)).1
    convert this using 3
  exact (hcrit _).2 (by convert key using 3)

/-- The local Frobenius forms are compatible with restriction. -/
theorem frobeniusForm_map {Õ Õ' : D.𝒱.Opens} (h : C.IsBasic Õ) (h' : C.IsBasic Õ') (hle : Õ' ≤ Õ)
    (ω : Γ(f.relativeDifferentialForms ((1 : ℕ) : ℤ), D.pieceAffine Õ h.isAffineOpen_inf_U)) :
    C.frobeniusForm h' ((f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
        (homOfLE (D.pieceAffine_le hle h.isAffineOpen_inf_U h'.isAffineOpen_inf_U)).op ω) =
      (f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
        (homOfLE (D.pieceAffine_le hle h.isAffineOpen_inf_U h'.isAffineOpen_inf_U)).op
          (C.frobeniusForm h ω) := by
  have hA : ((D.pieceAffine Õ' h'.isAffineOpen_inf_U) : V.Opens) ≤
      (D.pieceAffine Õ h.isAffineOpen_inf_U) :=
    D.pieceAffine_le hle h.isAffineOpen_inf_U h'.isAffineOpen_inf_U
  by_cases hL' : Nontrivial Γ(V, (D.pieceAffine Õ' h'.isAffineOpen_inf_U))
  swap
  · exact relativeDifferentialForms_eq_of_not_nontrivial hL' _ _
  have : Nontrivial Γ(V, (D.pieceAffine Õ h.isAffineOpen_inf_U)) := nontrivial_of_le D hA
  have := charP_of_nontrivial D (D.pieceAffine Õ h.isAffineOpen_inf_U)
  have := charP_of_nontrivial D (D.pieceAffine Õ' h'.isAffineOpen_inf_U)
  let := MMP.Mori.sectionAlgebra f (D.pieceAffine Õ h.isAffineOpen_inf_U)
  let := MMP.Mori.sectionAlgebra f (D.pieceAffine Õ' h'.isAffineOpen_inf_U)
  let : Algebra Γ(V, (D.pieceAffine Õ h.isAffineOpen_inf_U))
      Γ(V, (D.pieceAffine Õ' h'.isAffineOpen_inf_U)) :=
    (V.presheaf.map (homOfLE hA).op).hom.toAlgebra
  have := MMP.Flips.ResolutionInputs.isScalarTower_section_res f hA
  refine (formsAlgEquiv f 1 (D.pieceAffine Õ' h'.isAffineOpen_inf_U)).injective ?_
  rw [C.formsAlgEquiv_frobeniusForm h', formsAlgEquiv_restrict f 1 hA,
    formsAlgEquiv_restrict f 1 hA, C.formsAlgEquiv_frobeniusForm h]
  have := frobeniusLiftForm_mapExteriorPower k
    (D.𝒱.presheaf.map (homOfLE (inf_le_inf_right _ hle)).op).hom
    (D.isReductionModP_pieceReductionAt Õ h.isAffineOpen_inf_U h.inf_U.isAffineOpen)
    (D.isReductionModP_pieceReductionAt Õ' h'.isAffineOpen_inf_U h'.inf_U.isAffineOpen)
    (C.isFrobeniusLift_liftOn h.inf_U) (C.isFrobeniusLift_liftOn h'.inf_U)
    (fun a => D.pieceReductionAt_map hle h.isAffineOpen_inf_U h'.isAffineOpen_inf_U a)
    (fun a => C.liftOn_map_of_le h.inf_U h'.inf_U _ a)
    (formsAlgEquiv f 1 (D.pieceAffine Õ h.isAffineOpen_inf_U) ω)
  convert this using 1

/-- **The local Frobenius splitting on a piece of a chart**: the section of `K¹` whose form on
`U` is `φ = F̃^*/p` of the form of `s`. -/
def phiPiece {Õ : D.𝒱.Opens} (h : C.IsBasic Õ) :
    Γ(D.K 1, D.i ⁻¹ᵁ Õ) →+ Γ(D.K 1, D.i ⁻¹ᵁ Õ) :=
  AddMonoidHom.mk' (fun s => (C.frobeniusForm_mem_range h s).choose) fun s s' => D.he_inj 1 _ (by
    rw [(C.frobeniusForm_mem_range h _).choose_spec, map_add, map_add, map_add,
      (C.frobeniusForm_mem_range h s).choose_spec, (C.frobeniusForm_mem_range h s').choose_spec])

/-- The form of `phiPiece s` is `frobeniusForm` of the form of `s`. -/
theorem e_phiPiece {Õ : D.𝒱.Opens} (h : C.IsBasic Õ) (s : Γ(D.K 1, D.i ⁻¹ᵁ Õ)) :
    D.e 1 _ (C.phiPiece h s) = C.frobeniusForm h (D.e 1 _ s) :=
  (C.frobeniusForm_mem_range h s).choose_spec

/-- `phiPiece` is `p`-semilinear. -/
theorem phiPiece_smul {Õ : D.𝒱.Opens} (h : C.IsBasic Õ) (r : Γ(V, D.i ⁻¹ᵁ Õ))
    (s : Γ(D.K 1, D.i ⁻¹ᵁ Õ)) : C.phiPiece h (r • s) = r ^ p • C.phiPiece h s := by
  refine D.he_inj 1 _ ?_
  rw [C.e_phiPiece, D.he_smul, D.he_smul, C.e_phiPiece, C.frobeniusForm_smul, map_pow]

/-- `phiPiece` is compatible with restriction. -/
theorem phiPiece_map {Õ Õ' : D.𝒱.Opens} (h : C.IsBasic Õ) (h' : C.IsBasic Õ') (hle : Õ' ≤ Õ)
    (s : Γ(D.K 1, D.i ⁻¹ᵁ Õ)) :
    C.phiPiece h' ((D.K 1).presheaf.map (homOfLE (D.i.preimage_mono hle)).op s) =
      (D.K 1).presheaf.map (homOfLE (D.i.preimage_mono hle)).op (C.phiPiece h s) := by
  refine D.he_inj 1 _ ?_
  rw [C.e_phiPiece, D.he_res, D.he_res, C.e_phiPiece]
  exact C.frobeniusForm_map h h' hle _

/-- On a basic open of a chart, the ideal of `I j` is generated by the restriction of `tⱼ`. -/
theorem ideal_I_eq_span_map {Õ : D.𝒱.Opens} (h : C.IsBasic Õ) (j : ι) :
    (D.I j).ideal ⟨Õ, h.isAffineOpen⟩ =
      Ideal.span {D.𝒱.presheaf.map (homOfLE h.le).op (C.t j)} := by
  have := (D.I j).map_ideal (U := ⟨Õ, h.isAffineOpen⟩) (V := ⟨C.𝒲, C.isAffineOpen⟩) h.le
  rw [← this, C.ideal_eq, Ideal.map_span, Set.image_singleton]
  rfl

end FrobeniusLiftChart

/-! ### The homotopies between two charts -/

section Homotopy

variable {D} (C₁ C₂ : D.FrobeniusLiftChart)

open scoped Classical in
/-- **The homotopy `η₁₂` between the Frobenius forms of two charts** on a piece `i⁻¹Õ ⊓ U`
basic in both, read on sections (zero when the piece is empty). -/
def homotopyForm {Õ : D.𝒱.Opens} (h₁ : C₁.IsBasic Õ) (h₂ : C₂.IsBasic Õ) :
    Γ(f.relativeDifferentialForms ((1 : ℕ) : ℤ), D.pieceAffine Õ h₁.isAffineOpen_inf_U) →+
      Γ(f.relativeDifferentialForms ((0 : ℕ) : ℤ), D.pieceAffine Õ h₁.isAffineOpen_inf_U) :=
  letI := MMP.Mori.sectionAlgebra f (D.pieceAffine Õ h₁.isAffineOpen_inf_U)
  if hL : Nontrivial Γ(V, D.pieceAffine Õ h₁.isAffineOpen_inf_U) then
    haveI := charP_of_nontrivial D (D.pieceAffine Õ h₁.isAffineOpen_inf_U)
    (formsAlgEquiv f 0 (D.pieceAffine Õ h₁.isAffineOpen_inf_U)).symm.toAddMonoidHom.comp
      ((frobeniusLiftHomotopy k (D.isReductionModP_pieceReductionAt Õ h₁.isAffineOpen_inf_U
          h₁.inf_U.isAffineOpen) (C₁.isFrobeniusLift_liftOn h₁.inf_U)
          (C₂.isFrobeniusLift_liftOn h₂.inf_U)).toAddMonoidHom.comp
        (formsAlgEquiv f 1 (D.pieceAffine Õ h₁.isAffineOpen_inf_U)).toAddMonoidHom)
  else 0

/-- On a piece with nontrivial ring of functions, `homotopyForm` read in `⋀ Ω` is
`frobeniusLiftHomotopy` of the Frobenius lifts `liftOn` of the two charts. -/
theorem formsAlgEquiv_homotopyForm {Õ : D.𝒱.Opens} (h₁ : C₁.IsBasic Õ) (h₂ : C₂.IsBasic Õ)
    [hL : Nontrivial Γ(V, D.pieceAffine Õ h₁.isAffineOpen_inf_U)]
    (ω : Γ(f.relativeDifferentialForms ((1 : ℕ) : ℤ), D.pieceAffine Õ h₁.isAffineOpen_inf_U)) :
    letI := MMP.Mori.sectionAlgebra f (D.pieceAffine Õ h₁.isAffineOpen_inf_U)
    haveI := charP_of_nontrivial D (D.pieceAffine Õ h₁.isAffineOpen_inf_U)
    formsAlgEquiv f 0 (D.pieceAffine Õ h₁.isAffineOpen_inf_U) (homotopyForm C₁ C₂ h₁ h₂ ω) =
      frobeniusLiftHomotopy k (D.isReductionModP_pieceReductionAt Õ h₁.isAffineOpen_inf_U
          h₁.inf_U.isAffineOpen) (C₁.isFrobeniusLift_liftOn h₁.inf_U)
          (C₂.isFrobeniusLift_liftOn h₂.inf_U)
        (formsAlgEquiv f 1 (D.pieceAffine Õ h₁.isAffineOpen_inf_U) ω) := by
  classical
  rw [homotopyForm, dite_eq_left hL]
  simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

/-- `homotopyForm` is `p`-semilinear. -/
theorem homotopyForm_smul {Õ : D.𝒱.Opens} (h₁ : C₁.IsBasic Õ) (h₂ : C₂.IsBasic Õ)
    (c : Γ(V, D.pieceAffine Õ h₁.isAffineOpen_inf_U))
    (ω : Γ(f.relativeDifferentialForms ((1 : ℕ) : ℤ), D.pieceAffine Õ h₁.isAffineOpen_inf_U)) :
    homotopyForm C₁ C₂ h₁ h₂ (c • ω) = c ^ p • homotopyForm C₁ C₂ h₁ h₂ ω := by
  classical
  by_cases hL : Nontrivial Γ(V, D.pieceAffine Õ h₁.isAffineOpen_inf_U)
  · let := MMP.Mori.sectionAlgebra f (D.pieceAffine Õ h₁.isAffineOpen_inf_U)
    have := charP_of_nontrivial D (D.pieceAffine Õ h₁.isAffineOpen_inf_U)
    rw [homotopyForm, dite_eq_left hL]
    have := conj_frobeniusLiftHomotopy_smul k
      (D.isReductionModP_pieceReductionAt Õ h₁.isAffineOpen_inf_U h₁.inf_U.isAffineOpen)
      (C₁.isFrobeniusLift_liftOn h₁.inf_U) (C₂.isFrobeniusLift_liftOn h₂.inf_U)
      (formsAlgEquiv f 1 (D.pieceAffine Õ h₁.isAffineOpen_inf_U))
      (formsAlgEquiv f 0 (D.pieceAffine Õ h₁.isAffineOpen_inf_U)) c ω
    convert this using 1
  · exact relativeDifferentialForms_eq_of_not_nontrivial hL _ _

/-- The homotopy `η₁₂` of the form of a section of `K¹` over `i⁻¹Õ` is the form of a section of
`K⁰` over `i⁻¹Õ`. -/
theorem homotopyForm_mem_range {Õ : D.𝒱.Opens} (h₁ : C₁.IsBasic Õ) (h₂ : C₂.IsBasic Õ)
    (s : Γ(D.K 1, D.i ⁻¹ᵁ Õ)) :
    homotopyForm C₁ C₂ h₁ h₂ (D.e 1 _ s) ∈ Set.range (D.e 0 (D.i ⁻¹ᵁ Õ)) := by
  classical
  by_cases hL : Nontrivial Γ(V, D.pieceAffine Õ h₁.isAffineOpen_inf_U)
  swap
  · rw [homotopyForm, dite_eq_right hL]
    exact ⟨0, map_zero _⟩
  have hcrit1 := D.mem_range_e_iff ⟨D.i ⁻¹ᵁ Õ, D.isAffineOpen_preimage h₁.isAffineOpen⟩
    (C₁.u h₁.le) (C₁.ideal_J_eq_span_u h₁) 1
  have hcrit0 := D.mem_range_e_iff ⟨D.i ⁻¹ᵁ Õ, D.isAffineOpen_preimage h₁.isAffineOpen⟩
    (C₁.u h₁.le) (C₁.ideal_J_eq_span_u h₁) 0
  have hs := (hcrit1 (D.e 1 _ s)).1 ⟨s, rfl⟩
  let := MMP.Mori.sectionAlgebra f (D.pieceAffine Õ h₁.isAffineOpen_inf_U)
  let : Algebra Γ(V, D.i ⁻¹ᵁ Õ) Γ(V, D.pieceAffine Õ h₁.isAffineOpen_inf_U) :=
    (V.presheaf.map (homOfLE (inf_le_left : D.i ⁻¹ᵁ Õ ⊓ D.U ≤ D.i ⁻¹ᵁ Õ)).op).hom.toAlgebra
  have := charP_of_nontrivial D (D.pieceAffine Õ h₁.isAffineOpen_inf_U)
  have hGt : ∀ j, ∃ c, C₂.liftOn h₂ (D.𝒱.presheaf.map (homOfLE h₁.le).op (C₁.t j)) -
      C₁.liftOn h₁ (D.𝒱.presheaf.map (homOfLE h₁.le).op (C₁.t j)) =
        p * ((D.𝒱.presheaf.map (homOfLE h₁.le).op (C₁.t j)) ^ p * c) := by
    intro j
    have hI := (C₁.ideal_I_eq_span_map h₁ j).symm.trans (C₂.ideal_I_eq_span_map h₂ j)
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1
      (hI ▸ Ideal.mem_span_singleton_self (D.𝒱.presheaf.map (homOfLE h₁.le).op (C₁.t j)))
    obtain ⟨w', hw'⟩ := Ideal.mem_span_singleton'.1
      (hI.symm ▸ Ideal.mem_span_singleton_self (D.𝒱.presheaf.map (homOfLE h₂.le).op (C₂.t j)))
    exact exists_sub_eq_natCast_mul_pow_mul (C₂.isFrobeniusLift_liftOn h₂) (C₁.liftOn_t h₁ j)
      (C₂.liftOn_t h₂ j) hw.symm hw'.symm
  have key : ((formsAlgEquiv f 0 (D.pieceAffine Õ h₁.isAffineOpen_inf_U)
      (homotopyForm C₁ C₂ h₁ h₂ (D.e 1 _ s)) :
      ⋀[Γ(V, D.pieceAffine Õ h₁.isAffineOpen_inf_U)]^0
        (Ω[Γ(V, D.pieceAffine Õ h₁.isAffineOpen_inf_U)⁄k])) :
        ExteriorAlgebra Γ(V, D.pieceAffine Õ h₁.isAffineOpen_inf_U)
          (Ω[Γ(V, D.pieceAffine Õ h₁.isAffineOpen_inf_U)⁄k])) ∈
      logForms k Γ(V, D.pieceAffine Õ h₁.isAffineOpen_inf_U) (C₁.u h₁.le) 0 := by
    rw [formsAlgEquiv_homotopyForm]
    have := frobeniusLiftHomotopy_mem_logForms_of_map k (u := C₁.u h₁.le)
      (D.isReductionModP_pieceReductionAt Õ h₁.isAffineOpen_inf_U h₁.inf_U.isAffineOpen)
      (C₁.isFrobeniusLift_liftOn h₁.inf_U) (C₂.isFrobeniusLift_liftOn h₂.inf_U)
      (D.isReductionModP_app Õ h₁.isAffineOpen).surjective
      (D.𝒱.presheaf.map (homOfLE (inf_le_left : Õ ⊓ D.liftOpen D.U ≤ Õ)).op).hom
      (D.pieceReduction_map_app Õ) (C₁.isFrobeniusLift_liftOn h₁)
      (C₂.isFrobeniusLift_liftOn h₂) (C₁.liftOn_map_of_le h₁ h₁.inf_U inf_le_left)
      (C₂.liftOn_map_of_le h₂ h₂.inf_U inf_le_left)
      (fun j => D.𝒱.presheaf.map (homOfLE h₁.le).op (C₁.t j)) (fun _ => rfl) hGt
      (formsAlgEquiv f 1 (D.pieceAffine Õ h₁.isAffineOpen_inf_U) (D.e 1 _ s))
      (by convert hs using 3)
    convert this using 3
  exact (hcrit0 _).2 (by convert key using 3)

/-- The homotopies are compatible with restriction. -/
theorem homotopyForm_map {Õ Õ' : D.𝒱.Opens} (h₁ : C₁.IsBasic Õ) (h₂ : C₂.IsBasic Õ)
    (h₁' : C₁.IsBasic Õ') (h₂' : C₂.IsBasic Õ') (hle : Õ' ≤ Õ)
    (ω : Γ(f.relativeDifferentialForms ((1 : ℕ) : ℤ), D.pieceAffine Õ h₁.isAffineOpen_inf_U)) :
    homotopyForm C₁ C₂ h₁' h₂' ((f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
        (homOfLE (D.pieceAffine_le hle h₁.isAffineOpen_inf_U h₁'.isAffineOpen_inf_U)).op ω) =
      (f.relativeDifferentialForms ((0 : ℕ) : ℤ)).presheaf.map
        (homOfLE (D.pieceAffine_le hle h₁.isAffineOpen_inf_U h₁'.isAffineOpen_inf_U)).op
          (homotopyForm C₁ C₂ h₁ h₂ ω) := by
  have hA := D.pieceAffine_le hle h₁.isAffineOpen_inf_U h₁'.isAffineOpen_inf_U
  by_cases hL' : Nontrivial Γ(V, D.pieceAffine Õ' h₁'.isAffineOpen_inf_U)
  swap
  · exact relativeDifferentialForms_eq_of_not_nontrivial hL' _ _
  have : Nontrivial Γ(V, D.pieceAffine Õ h₁.isAffineOpen_inf_U) := nontrivial_of_le D hA
  have := charP_of_nontrivial D (D.pieceAffine Õ h₁.isAffineOpen_inf_U)
  have := charP_of_nontrivial D (D.pieceAffine Õ' h₁'.isAffineOpen_inf_U)
  let := MMP.Mori.sectionAlgebra f (D.pieceAffine Õ h₁.isAffineOpen_inf_U)
  let := MMP.Mori.sectionAlgebra f (D.pieceAffine Õ' h₁'.isAffineOpen_inf_U)
  let : Algebra Γ(V, D.pieceAffine Õ h₁.isAffineOpen_inf_U)
      Γ(V, D.pieceAffine Õ' h₁'.isAffineOpen_inf_U) :=
    (V.presheaf.map (homOfLE hA).op).hom.toAlgebra
  have := MMP.Flips.ResolutionInputs.isScalarTower_section_res f hA
  refine (formsAlgEquiv f 0 (D.pieceAffine Õ' h₁'.isAffineOpen_inf_U)).injective ?_
  rw [formsAlgEquiv_homotopyForm, formsAlgEquiv_restrict f 1 hA,
    formsAlgEquiv_restrict f 0 hA, formsAlgEquiv_homotopyForm]
  have := frobeniusLiftHomotopy_mapExteriorPower k
    (D.𝒱.presheaf.map (homOfLE (inf_le_inf_right _ hle)).op).hom
    (D.isReductionModP_pieceReductionAt Õ h₁.isAffineOpen_inf_U h₁.inf_U.isAffineOpen)
    (D.isReductionModP_pieceReductionAt Õ' h₁'.isAffineOpen_inf_U h₁'.inf_U.isAffineOpen)
    (C₁.isFrobeniusLift_liftOn h₁.inf_U) (C₂.isFrobeniusLift_liftOn h₂.inf_U)
    (C₁.isFrobeniusLift_liftOn h₁'.inf_U) (C₂.isFrobeniusLift_liftOn h₂'.inf_U)
    (fun a => D.pieceReductionAt_map hle h₁.isAffineOpen_inf_U h₁'.isAffineOpen_inf_U a)
    (fun a => C₁.liftOn_map_of_le h₁.inf_U h₁'.inf_U _ a)
    (fun a => C₂.liftOn_map_of_le h₂.inf_U h₂'.inf_U _ a)
    (formsAlgEquiv f 1 (D.pieceAffine Õ h₁.isAffineOpen_inf_U) ω)
  convert this using 1

/-- **`φ₂ - φ₁ = d ∘ η₁₂`** on a piece basic in two charts. -/
theorem frobeniusForm_sub_frobeniusForm {Õ : D.𝒱.Opens} (h₁ : C₁.IsBasic Õ) (h₂ : C₂.IsBasic Õ)
    (ω : Γ(f.relativeDifferentialForms ((1 : ℕ) : ℤ), D.pieceAffine Õ h₁.isAffineOpen_inf_U)) :
    C₂.frobeniusForm h₂ ω - C₁.frobeniusForm h₁ ω =
      ((f.deRhamComplex).d 0 (0 + 1)).val.app
        (op (D.i ⁻¹ᵁ Õ ⊓ D.U)) (homotopyForm C₁ C₂ h₁ h₂ ω) := by
  by_cases hL : Nontrivial Γ(V, D.pieceAffine Õ h₁.isAffineOpen_inf_U)
  swap
  · exact relativeDifferentialForms_eq_of_not_nontrivial hL _ _
  have := charP_of_nontrivial D (D.pieceAffine Õ h₁.isAffineOpen_inf_U)
  let := MMP.Mori.sectionAlgebra f (D.pieceAffine Õ h₁.isAffineOpen_inf_U)
  refine (formsAlgEquiv f 1 (D.pieceAffine Õ h₁.isAffineOpen_inf_U)).injective ?_
  have hd := formsAlgEquiv_d f 0 (D.pieceAffine Õ h₁.isAffineOpen_inf_U)
    (homotopyForm C₁ C₂ h₁ h₂ ω)
  rw [map_sub, C₁.formsAlgEquiv_frobeniusForm h₁, C₂.formsAlgEquiv_frobeniusForm h₂]
  rw [formsAlgEquiv_homotopyForm] at hd
  have := frobeniusLiftForm_sub_frobeniusLiftForm k
    (D.isReductionModP_pieceReductionAt Õ h₁.isAffineOpen_inf_U h₁.inf_U.isAffineOpen)
    (C₁.isFrobeniusLift_liftOn h₁.inf_U) (C₂.isFrobeniusLift_liftOn h₂.inf_U)
    (formsAlgEquiv f 1 (D.pieceAffine Õ h₁.isAffineOpen_inf_U) ω)
  convert this.trans hd.symm using 1

/-- **The cocycle relation `η₁₂ + η₂₃ = η₁₃`** on a piece basic in three charts. -/
theorem homotopyForm_add_homotopyForm (C₃ : D.FrobeniusLiftChart) {Õ : D.𝒱.Opens}
    (h₁ : C₁.IsBasic Õ) (h₂ : C₂.IsBasic Õ) (h₃ : C₃.IsBasic Õ)
    (ω : Γ(f.relativeDifferentialForms ((1 : ℕ) : ℤ), D.pieceAffine Õ h₁.isAffineOpen_inf_U)) :
    homotopyForm C₁ C₂ h₁ h₂ ω + homotopyForm C₂ C₃ h₂ h₃ ω = homotopyForm C₁ C₃ h₁ h₃ ω := by
  by_cases hL : Nontrivial Γ(V, D.pieceAffine Õ h₁.isAffineOpen_inf_U)
  swap
  · exact relativeDifferentialForms_eq_of_not_nontrivial hL _ _
  have := charP_of_nontrivial D (D.pieceAffine Õ h₁.isAffineOpen_inf_U)
  let := MMP.Mori.sectionAlgebra f (D.pieceAffine Õ h₁.isAffineOpen_inf_U)
  refine (formsAlgEquiv f 0 (D.pieceAffine Õ h₁.isAffineOpen_inf_U)).injective ?_
  rw [map_add, formsAlgEquiv_homotopyForm, formsAlgEquiv_homotopyForm, formsAlgEquiv_homotopyForm]
  have := frobeniusLiftHomotopy_add_frobeniusLiftHomotopy k
    (D.isReductionModP_pieceReductionAt Õ h₁.isAffineOpen_inf_U h₁.inf_U.isAffineOpen)
    (C₁.isFrobeniusLift_liftOn h₁.inf_U) (C₂.isFrobeniusLift_liftOn h₂.inf_U)
    (C₃.isFrobeniusLift_liftOn h₃.inf_U)
    (formsAlgEquiv f 1 (D.pieceAffine Õ h₁.isAffineOpen_inf_U) ω)
  convert this using 1

/-- **The local homotopy on a piece of two charts**: the function on `i⁻¹Õ` whose restriction to
`U` is `η₁₂` of the form of `s`. -/
def etaPiece {Õ : D.𝒱.Opens} (h₁ : C₁.IsBasic Õ) (h₂ : C₂.IsBasic Õ) :
    Γ(D.K 1, D.i ⁻¹ᵁ Õ) →+ Γ(D.K 0, D.i ⁻¹ᵁ Õ) :=
  AddMonoidHom.mk' (fun s => (homotopyForm_mem_range C₁ C₂ h₁ h₂ s).choose) fun s s' =>
    D.he_inj 0 _ (by
      rw [(homotopyForm_mem_range C₁ C₂ h₁ h₂ _).choose_spec, map_add, map_add, map_add,
        (homotopyForm_mem_range C₁ C₂ h₁ h₂ s).choose_spec,
        (homotopyForm_mem_range C₁ C₂ h₁ h₂ s').choose_spec])

/-- The form of `etaPiece s` is `homotopyForm` of the form of `s`. -/
theorem e_etaPiece {Õ : D.𝒱.Opens} (h₁ : C₁.IsBasic Õ) (h₂ : C₂.IsBasic Õ)
    (s : Γ(D.K 1, D.i ⁻¹ᵁ Õ)) :
    D.e 0 _ (etaPiece C₁ C₂ h₁ h₂ s) = homotopyForm C₁ C₂ h₁ h₂ (D.e 1 _ s) :=
  (homotopyForm_mem_range C₁ C₂ h₁ h₂ s).choose_spec

/-- `etaPiece` is `p`-semilinear. -/
theorem etaPiece_smul {Õ : D.𝒱.Opens} (h₁ : C₁.IsBasic Õ) (h₂ : C₂.IsBasic Õ)
    (r : Γ(V, D.i ⁻¹ᵁ Õ)) (s : Γ(D.K 1, D.i ⁻¹ᵁ Õ)) :
    etaPiece C₁ C₂ h₁ h₂ (r • s) = r ^ p • etaPiece C₁ C₂ h₁ h₂ s := by
  refine D.he_inj 0 _ ?_
  rw [e_etaPiece, D.he_smul, D.he_smul, e_etaPiece, homotopyForm_smul, map_pow]

/-- `etaPiece` is compatible with restriction. -/
theorem etaPiece_map {Õ Õ' : D.𝒱.Opens} (h₁ : C₁.IsBasic Õ) (h₂ : C₂.IsBasic Õ)
    (h₁' : C₁.IsBasic Õ') (h₂' : C₂.IsBasic Õ') (hle : Õ' ≤ Õ) (s : Γ(D.K 1, D.i ⁻¹ᵁ Õ)) :
    etaPiece C₁ C₂ h₁' h₂' ((D.K 1).presheaf.map (homOfLE (D.i.preimage_mono hle)).op s) =
      (D.K 0).presheaf.map (homOfLE (D.i.preimage_mono hle)).op (etaPiece C₁ C₂ h₁ h₂ s) := by
  refine D.he_inj 0 _ ?_
  rw [e_etaPiece, D.he_res, D.he_res, e_etaPiece]
  exact homotopyForm_map C₁ C₂ h₁ h₂ h₁' h₂' hle _

/-- **`φ₂ - φ₁ = d ∘ η₁₂`** on the sections of `K¹` over a piece of two charts. -/
theorem phiPiece_sub_phiPiece {Õ : D.𝒱.Opens} (h₁ : C₁.IsBasic Õ) (h₂ : C₂.IsBasic Õ)
    (s : Γ(D.K 1, D.i ⁻¹ᵁ Õ)) :
    C₂.phiPiece h₂ s - C₁.phiPiece h₁ s = (D.d 0).app (D.i ⁻¹ᵁ Õ) (etaPiece C₁ C₂ h₁ h₂ s) := by
  refine D.he_inj 1 _ ((map_sub _ _ _).trans ?_)
  rw [C₂.e_phiPiece, C₁.e_phiPiece]
  refine (frobeniusForm_sub_frobeniusForm C₁ C₂ h₁ h₂ _).trans ?_
  refine Eq.trans ?_ (D.he_d 0 (D.i ⁻¹ᵁ Õ) (etaPiece C₁ C₂ h₁ h₂ s)).symm
  exact congrArg _ (e_etaPiece C₁ C₂ h₁ h₂ s).symm

/-- **The cocycle relation** on the sections of `K¹` over a piece of three charts. -/
theorem etaPiece_add_etaPiece (C₃ : D.FrobeniusLiftChart) {Õ : D.𝒱.Opens}
    (h₁ : C₁.IsBasic Õ) (h₂ : C₂.IsBasic Õ) (h₃ : C₃.IsBasic Õ) (s : Γ(D.K 1, D.i ⁻¹ᵁ Õ)) :
    etaPiece C₁ C₂ h₁ h₂ s + etaPiece C₂ C₃ h₂ h₃ s = etaPiece C₁ C₃ h₁ h₃ s := by
  refine D.he_inj 0 _ ((map_add _ _ _).trans ?_)
  rw [e_etaPiece, e_etaPiece, e_etaPiece]
  exact homotopyForm_add_homotopyForm C₁ C₂ C₃ h₁ h₂ h₃ _

end Homotopy

end FrobeniusSplittingData

end MMP.DeRham
