module

public import MMP.AlgebraicGeometry.DeRham.FrobeniusSplittingGlue
public import MMP.AlgebraicGeometry.DeRham.EtaleLogCoordinates
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# Charts with Frobenius lifts exist

Let `V` be a smooth `k`-scheme with a simple normal crossing divisor `∑ⱼ V(J j)`, and `𝒱` a
lifting of `V` and of the divisor over `W₂(k)` (`MMP.DeRham.FrobeniusSplittingData`). Every point
`x` of `V` lies in a chart with a Frobenius lift
(`MMP.DeRham.FrobeniusSplittingData.FrobeniusLiftChart`): an affine open `𝒲` of `𝒱` through
`x`, generators `t̃ⱼ` of the ideals of the lifted components on `𝒲`, and a Frobenius lift `F` on
`Γ(𝒱, 𝒲)` with `F t̃ⱼ = t̃ⱼ ^ p`.

The proof follows Deligne–Illusie. Take a chart of the divisor on `V` around `x` with equations
`tⱼ` and étale coordinates `s₁, …, sₘ` containing the `tⱼ` through `x`, and a basic open `𝒲` of
an affine open of `𝒱` over it. Lift the `tⱼ` to `t̃ⱼ` in the ideals of the lifted components:
since the lifted components are flat over `W₂(k)` and `p ^ 2 = 0`, a lift of a generator modulo
`p` generates (`MMP.DeRham.ideal_eq_span_singleton_of_le_sup_span`). Since `Γ(𝒱, 𝒲)` is formally
smooth over `W₂(k)` it has a Frobenius lift `F₀`; correcting `F₀` by `p` times the Frobenius
derivation `a ↦ ∑ᵢ (∂ᵢ a)ᵖ cᵢ`, with `∂ᵢ` the derivations dual to the étale coordinates, gives a
Frobenius lift fixing the coordinates up to `p`-th powers
(`MMP.DeRham.exists_isFrobeniusLift_eq_pow_of_formallyEtale`).

## Main results

* `MMP.DeRham.exists_isFrobeniusLift_eq_pow_of_formallyEtale`: Frobenius lifts with
  `F sᵢ = sᵢ ^ p` along coordinates that are étale modulo `p`.
* `MMP.DeRham.FrobeniusSplittingData.exists_frobeniusLiftChart`: every point lies in a chart
  with a Frobenius lift.
* `MMP.DeRham.FrobeniusSplittingData.nonempty_localFrobeniusSplitting`: the local Frobenius
  splitting exists.

## Implementation notes

Formal smoothness of `W₂(k)[X] → Γ(𝒱, 𝒲)` is not needed: the correction of an arbitrary
Frobenius lift uses only the étale coordinates modulo `p`.

## References

* [P. Deligne, L. Illusie, *Relèvements modulo p² et décomposition du complexe de de Rham*,
  Invent. Math. 89 (1987)][DeligneIllusie1987], §2.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v

namespace MMP.DeRham

section RingLevel

variable {T : Type*} [CommRing T] {p : ℕ}

/-- **Generators modulo `p` generate**, for an ideal `I` with `T ⧸ I` flat over a ring in which
`p ^ 2 = 0` (stated through `p a ∈ I → a ∈ I + pT`): if `u ∈ I` generates `I` modulo `p`, then
it generates `I`. -/
theorem ideal_eq_span_singleton_of_le_sup_span (hp2 : (p : T) ^ 2 = 0) {I : Ideal T} {u : T}
    (hflat : ∀ a, (p : T) * a ∈ I → a ∈ I ⊔ Ideal.span {(p : T)}) (hu : u ∈ I)
    (hle : I ≤ Ideal.span {u} ⊔ Ideal.span {(p : T)}) : I = Ideal.span {u} := by
  refine le_antisymm (fun y hy => ?_) ((Ideal.span_singleton_le_iff_mem _).2 hu)
  obtain ⟨a, b, hb, rfl⟩ := Ideal.mem_span_singleton_sup.1 (hle hy)
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
  have hc : (p : T) * c ∈ I := by
    rw [show (p : T) * c = a * u + c * p - a * u by ring]
    exact I.sub_mem hy (I.mul_mem_left _ hu)
  obtain ⟨i₁, hi₁, z, hz, hcz⟩ := Submodule.mem_sup.1 (hflat c hc)
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  obtain ⟨a', b', hb', hi⟩ := Ideal.mem_span_singleton_sup.1 (hle hi₁)
  obtain ⟨c', rfl⟩ := Ideal.mem_span_singleton'.1 hb'
  refine Ideal.mem_span_singleton'.2 ⟨a + p * a', ?_⟩
  rw [← hcz, ← hi]
  linear_combination (-(d) - c') * hp2

/-- An element whose image modulo a square-zero `p` is a unit is a unit. -/
theorem isUnit_of_isUnit_map (hp2 : (p : T) ^ 2 = 0) {B : Type*} [CommRing B] (π : T →+* B)
    (hker : RingHom.ker π = Ideal.span {(p : T)}) (hπ : Function.Surjective π) {u : T}
    (hu : IsUnit (π u)) : IsUnit u := by
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  obtain ⟨v, rfl⟩ := hπ w
  have h1 : u * v - 1 ∈ RingHom.ker π := by
    rw [RingHom.mem_ker, map_sub, map_mul, hw, map_one, sub_self]
  rw [hker] at h1
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
  refine isUnit_iff_exists_inv.2 ⟨v * (1 - c * p), ?_⟩
  linear_combination (1 - c * p) * hc.symm - c ^ 2 * hp2

/-- Multiplication by a square-zero `p` only sees the reduction modulo `p`. -/
theorem natCast_mul_eq_of_map_eq (hp2 : (p : T) ^ 2 = 0) {B : Type*} [CommRing B] {π : T →+* B}
    (hker : RingHom.ker π = Ideal.span {(p : T)}) {a a' : T} (h : π a = π a') :
    (p : T) * a = p * a' := by
  have : a - a' ∈ RingHom.ker π := by rw [RingHom.mem_ker, map_sub, h, sub_self]
  rw [hker] at this
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 this
  linear_combination (-p) * hc + c * hp2

open KaehlerDifferential in
/-- **Coordinate derivations.** If `k[X] → B`, `Xᵢ ↦ sᵢ`, is formally étale, there are
derivations `∂ᵢ` of `B` with `∂ᵢ sⱼ = δᵢⱼ`. -/
theorem exists_coordinate_derivations {k B σ : Type*} [CommRing k] [CommRing B] [Algebra k B]
    [DecidableEq σ] (s : σ → B) (hs : (MvPolynomial.aeval (R := k) s).toRingHom.FormallyEtale) :
    ∃ c : σ → B → B, (∀ i a b, c i (a + b) = c i a + c i b) ∧
      (∀ i a b, c i (a * b) = a * c i b + b * c i a) ∧
      ∀ i j, c i (s j) = if j = i then 1 else 0 := by
  let φ := (MvPolynomial.aeval (R := k) s).toRingHom
  let : Algebra (MvPolynomial σ k) B := φ.toAlgebra
  have : IsScalarTower k (MvPolynomial σ k) B := IsScalarTower.of_algebraMap_eq fun r => by
    simp [RingHom.algebraMap_toAlgebra, φ]
  have : Algebra.FormallyEtale (MvPolynomial σ k) B := hs
  let b := (isBaseChange_of_formallyEtale k (MvPolynomial σ k) B).basis (mvPolynomialBasis k σ)
  have hb : ∀ i, b i = D k B (s i) := fun i => by
    rw [IsBaseChange.basis_apply, mvPolynomialBasis_apply]
    simp [RingHom.algebraMap_toAlgebra, φ]
  refine ⟨fun i a => b.coord i (D k B a), fun i a a' => by simp, fun i a a' => ?_,
    fun i j => ?_⟩
  · simp only [Derivation.leibniz, map_add, map_smul, smul_eq_mul]
  · change b.coord i (D k B (s j)) = _
    rw [← hb, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

/-- **Correcting a Frobenius lift by a Frobenius derivation.** Let `p ^ 2 = 0` in `T`, `π : T → B`
reduction modulo `p`, and `F₀` a Frobenius lift on `T`. If `δ : B → B` is additive with
`δ (a b) = aᵖ δ b + bᵖ δ a`, then `a ↦ F₀ a + p δ(π a)` is a Frobenius lift. -/
theorem exists_isFrobeniusLift_add_natCast_mul {B : Type*} [CommRing B] (hp2 : (p : T) ^ 2 = 0)
    (π : T →+* B) (hπ : Function.Surjective π) (hker : RingHom.ker π = Ideal.span {(p : T)})
    {F₀ : T →+* T} (hF₀ : IsFrobeniusLift p F₀) (δ : B → B)
    (hδadd : ∀ a b, δ (a + b) = δ a + δ b) (hδmul : ∀ a b, δ (a * b) = a ^ p * δ b + b ^ p * δ a) :
    ∃ F : T →+* T, IsFrobeniusLift p F ∧ ∀ a, F a = F₀ a + p * Function.surjInv hπ (δ (π a)) := by
  let L := Function.surjInv hπ
  have hL : ∀ b, π (L b) = b := Function.surjInv_eq hπ
  have hFπ : ∀ a, π (F₀ a) = π a ^ p := fun a => by
    have : F₀ a - a ^ p ∈ RingHom.ker π := hker ▸ hF₀ a
    rwa [RingHom.mem_ker, map_sub, sub_eq_zero, map_pow] at this
  have hδ1 : δ 1 = 0 := by simpa using hδmul 1 1
  have hδ0 : δ 0 = 0 := by simpa using hδadd 0 0
  have wd : ∀ {a a' : T}, π a = π a' → (p : T) * a = p * a' := natCast_mul_eq_of_map_eq hp2 hker
  let F : T →+* T :=
    { toFun := fun a => F₀ a + p * L (δ (π a))
      map_one' := by
        simp only [map_one, hδ1]
        rw [wd (a' := 0) (by rw [hL, map_zero]), mul_zero, add_zero]
      map_mul' := fun a b => by
        simp only [map_mul, hδmul]
        have : (p : T) * L (π a ^ p * δ (π b) + π b ^ p * δ (π a)) =
            p * (F₀ a * L (δ (π b)) + F₀ b * L (δ (π a))) :=
          wd (by rw [hL, map_add, map_mul, map_mul, hL, hL, hFπ, hFπ])
        rw [this]
        linear_combination (- L (δ (π a)) * L (δ (π b))) * hp2
      map_zero' := by
        simp only [map_zero, hδ0]
        rw [wd (a' := 0) (by rw [hL, map_zero]), mul_zero, add_zero]
      map_add' := fun a b => by
        simp only [map_add, hδadd]
        rw [wd (a' := L (δ (π a)) + L (δ (π b))) (by rw [hL, map_add, hL, hL])]
        ring }
  refine ⟨F, fun a => ?_, fun a => rfl⟩
  change F₀ a + p * L (δ (π a)) - a ^ p ∈ _
  rw [show F₀ a + p * L (δ (π a)) - a ^ p = (F₀ a - a ^ p) + L (δ (π a)) * p by ring]
  exact Ideal.add_mem _ (hF₀ a) (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))

/-- **Frobenius lifts fixing étale coordinates.** Let `p ^ 2 = 0` in `T`, `π : T → B` reduction
modulo `p`, and `F₀` a Frobenius lift on `T`. If `k[X] → B`, `Xᵢ ↦ π sᵢ`, is formally étale
(finitely many `sᵢ`), then `F₀` can be corrected by `p` times a Frobenius derivation to a
Frobenius lift `F` with `F sᵢ = sᵢ ^ p`. -/
theorem exists_isFrobeniusLift_eq_pow_of_formallyEtale [hp : Fact p.Prime] {k B σ : Type*}
    [CommRing k] [CommRing B] [Algebra k B] [Finite σ] (hp2 : (p : T) ^ 2 = 0) (π : T →+* B)
    (hπ : Function.Surjective π) (hker : RingHom.ker π = Ideal.span {(p : T)}) {F₀ : T →+* T}
    (hF₀ : IsFrobeniusLift p F₀) (s : σ → T)
    (hs : (MvPolynomial.aeval (R := k) fun i => π (s i)).toRingHom.FormallyEtale) :
    ∃ F : T →+* T, IsFrobeniusLift p F ∧ ∀ i, F (s i) = s i ^ p := by
  classical
  have := Fintype.ofFinite σ
  obtain ⟨c, hcadd, hcmul, hcs⟩ := exists_coordinate_derivations (fun i => π (s i)) hs
  have hpker : (p : T) ∈ RingHom.ker π := hker ▸ Ideal.subset_span rfl
  have hpB : (p : B) = 0 := by simpa using hpker
  have hpow : ∀ x y : B, (x + y) ^ p = x ^ p + y ^ p := add_pow_of_natCast_eq_zero hp.out hpB
  choose h hh using fun i => Ideal.mem_span_singleton'.1 (hF₀ (s i))
  let δ : B → B := fun a => ∑ i, c i a ^ p * (-π (h i))
  have hδadd : ∀ a b, δ (a + b) = δ a + δ b := by
    intro a b
    simp only [δ, hcadd, hpow, add_mul, Finset.sum_add_distrib]
  have hδmul : ∀ a b, δ (a * b) = a ^ p * δ b + b ^ p * δ a := by
    intro a b
    simp only [δ, hcmul, hpow, mul_pow, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hδs : ∀ j, δ (π (s j)) = -π (h j) := by
    intro j
    simp only [δ, hcs]
    rw [Finset.sum_eq_single j (fun i _ hij => by
      rw [ite_eq_right_iff.2 (fun h => absurd h.symm hij), zero_pow hp.out.ne_zero, zero_mul])
      (by simp)]
    simp
  obtain ⟨F, hF, hFa⟩ := exists_isFrobeniusLift_add_natCast_mul hp2 π hπ hker hF₀ δ hδadd hδmul
  refine ⟨F, hF, fun j => ?_⟩
  rw [hFa, hδs, natCast_mul_eq_of_map_eq hp2 hker (a' := -h j)
    (by rw [Function.surjInv_eq hπ, map_neg])]
  linear_combination -(hh j)

/-- An ideal whose image modulo `p` lies in `(π u)` lies in `(u) + pT`. -/
theorem le_span_sup_span_of_map_le {B : Type*} [CommRing B] {π : T →+* B}
    (hπ : Function.Surjective π) (hker : RingHom.ker π = Ideal.span {(p : T)}) {I : Ideal T}
    {u : T} (h : I.map π ≤ Ideal.span {π u}) : I ≤ Ideal.span {u} ⊔ Ideal.span {(p : T)} := by
  rw [← hker, ← Ideal.comap_map_of_surjective' π hπ, Ideal.map_span, Set.image_singleton]
  exact Ideal.map_le_iff_le_comap.1 h

/-- A ring formally smooth over `W₂(k)` has a Frobenius lift. -/
theorem exists_isFrobeniusLift_of_formallySmooth_truncatedWittVector [Fact p.Prime] {k : Type*}
    [CommRing k] [CharP k p] [PerfectRing k p] [Algebra (TruncatedWittVector p 2 k) T]
    (h : (algebraMap (TruncatedWittVector p 2 k) T).FormallySmooth) :
    ∃ F : T →+* T, IsFrobeniusLift p F := by
  have hx : (MvPolynomial.aeval (R := TruncatedWittVector p 2 k)
      (Empty.elim : Empty → T)).toRingHom.FormallySmooth := by
    have : (MvPolynomial.aeval (R := TruncatedWittVector p 2 k) (Empty.elim : Empty → T)).toRingHom
        = (algebraMap (TruncatedWittVector p 2 k) T).comp
          (MvPolynomial.isEmptyAlgEquiv (TruncatedWittVector p 2 k) Empty).toRingEquiv.toRingHom :=
      MvPolynomial.ringHom_ext (fun r => by
        change (MvPolynomial.aeval Empty.elim) (MvPolynomial.C r) = algebraMap _ T
          ((MvPolynomial.isEmptyAlgEquiv _ Empty) (MvPolynomial.C r))
        rw [MvPolynomial.aeval_C, ← MvPolynomial.algebraMap_eq, AlgEquiv.commutes,
          Algebra.algebraMap_self, RingHom.id_apply]) (fun i => i.elim)
    rw [this]
    exact RingHom.FormallySmooth.comp (RingHom.FormallySmooth.of_bijective
      (MvPolynomial.isEmptyAlgEquiv _ Empty).bijective) h
  obtain ⟨F, hF, -, -⟩ := exists_isFrobeniusLift_truncatedWittVector p 2 k _ hx
  exact ⟨F, hF⟩

/-- **Étale coordinates on a localization.** If `k[X] → B_g`, `Xᵢ ↦ sᵢ`, is étale and `B'` is a
localization of `B` in which `g` is a unit, then `k[X] → B'` is formally étale. -/
theorem formallyEtale_aeval_of_isLocalization {k B B' σ : Type*} [CommRing k] [CommRing B]
    [CommRing B'] [Algebra k B] [Algebra B B'] [Algebra k B'] [IsScalarTower k B B']
    (s : σ → B) (g a : B) [IsLocalization.Away a B'] (hg : IsUnit (algebraMap B B' g))
    (het : (MvPolynomial.aeval (R := k) fun i =>
      algebraMap B (Localization.Away g) (s i)).toRingHom.Etale) :
    (MvPolynomial.aeval (R := k) fun i => algebraMap B B' (s i)).toRingHom.FormallyEtale := by
  let ψ : Localization.Away g →+* B' := IsLocalization.Away.lift g hg
  let : Algebra (Localization.Away g) B' := ψ.toAlgebra
  have : IsScalarTower B (Localization.Away g) B' := IsScalarTower.of_algebraMap_eq fun b =>
    (IsLocalization.Away.lift_eq g hg b).symm
  have : Algebra.FormallyEtale B B' := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers a)
  have : Algebra.FormallyEtale (Localization.Away g) B' :=
    Algebra.FormallyEtale.of_restrictScalars (R := B)
  have hψ : ψ.FormallyEtale := ‹Algebra.FormallyEtale (Localization.Away g) B'›
  have h1 : (MvPolynomial.aeval (R := k) fun i =>
      algebraMap B (Localization.Away g) (s i)).toRingHom.FormallyEtale := by
    let := (MvPolynomial.aeval (R := k) fun i =>
      algebraMap B (Localization.Away g) (s i)).toRingHom.toAlgebra
    have : Algebra.Etale _ _ := het
    exact Algebra.Etale.formallyEtale
  have heq : ψ.comp (MvPolynomial.aeval (R := k) fun i =>
      algebraMap B (Localization.Away g) (s i)).toRingHom =
      (MvPolynomial.aeval (R := k) fun i => algebraMap B B' (s i)).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.aeval_C]
      rw [IsScalarTower.algebraMap_apply k B (Localization.Away g), IsLocalization.Away.lift_eq,
        ← IsScalarTower.algebraMap_apply]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.aeval_X]
      exact IsLocalization.Away.lift_eq g hg _
  rw [← heq]
  exact RingHom.FormallyEtale.comp h1 hψ

end RingLevel

/-- A section is a unit on every open inside its basic open. -/
theorem isUnit_map_of_le_basicOpen {X : Scheme.{u}} {A B : X.Opens} (h : B ≤ A) (a : Γ(X, A))
    (hB : B ≤ X.basicOpen a) : IsUnit (X.presheaf.map (homOfLE h).op a) := by
  have := (X.toRingedSpace.isUnit_res_basicOpen a).map (X.presheaf.map (homOfLE hB).op).hom
  have e : X.presheaf.map (homOfLE h).op a = X.presheaf.map (homOfLE hB).op
      (X.presheaf.map (homOfLE (X.basicOpen_le a)).op a) :=
    (FrobeniusSplittingData.structureSheaf_map_map (X.basicOpen_le a) hB a).symm
  rwa [e]

namespace FrobeniusSplittingData

variable {p : ℕ} [Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectField k] {n : ℕ}
  {V : Scheme.{u}} {f : V ⟶ Spec (.of k)} [IsProper f] [SmoothOfRelativeDimension n f]
  {ι : Type v} [Fintype ι] [HasDerivedCategory.{u} V.Modules]
  (D : FrobeniusSplittingData p k n f ι)

/-- The sections of the lifting over an affine open are formally smooth over `W₂(k)`. -/
theorem formallySmooth_sectionsRingHom (Õ : D.𝒱.Opens) (hÕ : IsAffineOpen Õ) :
    (D.sectionsRingHom Õ).FormallySmooth :=
  RingHom.FormallySmooth.comp (RingHom.FormallySmooth.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv))
    (HasRingHomProperty.appLE @AlgebraicGeometry.Smooth D.g D.smooth_g ⟨⊤, isAffineOpen_top _⟩
      ⟨Õ, hÕ⟩ _).formallySmooth

/-- Since the lifted components are flat over `W₂(k)`, on an affine open `p a ∈ I j` forces
`a ∈ I j + p Γ(𝒱, Õ)`. -/
theorem mem_ideal_sup_of_natCast_mul_mem (j : ι) (Õ : D.𝒱.Opens) (hÕ : IsAffineOpen Õ)
    (a : Γ(D.𝒱, Õ)) (ha : (p : Γ(D.𝒱, Õ)) * a ∈ (D.I j).ideal ⟨Õ, hÕ⟩) :
    a ∈ (D.I j).ideal ⟨Õ, hÕ⟩ ⊔ Ideal.span {(p : Γ(D.𝒱, Õ))} := by
  have e : (⨆ j' ∈ ({j} : Finset ι), D.I j') = D.I j := by simp
  have hsm := (D.hI {j}).1
  rw [e] at hsm
  have hsmZ : Smooth ((D.I j).subschemeι ≫ D.g) :=
    SmoothOfRelativeDimension.smooth (n - ({j} : Finset ι).card) _
  set φ := ((D.I j).subschemeι.app Õ).hom
  have hker : RingHom.ker φ = (D.I j).ideal ⟨Õ, hÕ⟩ := (D.I j).ker_subschemeι_app ⟨Õ, hÕ⟩
  have hsurj : Function.Surjective φ := (D.I j).subschemeι.app_surjective Õ hÕ
  have hZ : IsAffineOpen ((D.I j).subschemeι ⁻¹ᵁ Õ) := hÕ.preimage _
  let ψ : TruncatedWittVector p 2 k →+* Γ((D.I j).subscheme, (D.I j).subschemeι ⁻¹ᵁ Õ) :=
    (((D.I j).subschemeι ≫ D.g).appLE ⊤ _ fun _ _ => trivial).hom.comp
      (Scheme.ΓSpecIso (.of (TruncatedWittVector p 2 k))).inv.hom
  let := ψ.toAlgebra
  have : Module.Flat (TruncatedWittVector p 2 k)
      Γ((D.I j).subscheme, (D.I j).subschemeι ⁻¹ᵁ Õ) :=
    RingHom.Flat.comp (RingHom.Flat.of_bijective
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv))
      (HasRingHomProperty.appLE @AlgebraicGeometry.Smooth _ hsmZ ⟨⊤, isAffineOpen_top _⟩
        ⟨_, hZ⟩ _).flat
  have h0 : (p : Γ((D.I j).subscheme, (D.I j).subschemeι ⁻¹ᵁ Õ)) * φ a = 0 := by
    rwa [← map_natCast φ, ← map_mul, ← RingHom.mem_ker, hker]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1
    (mem_span_natCast_of_natCast_mul_eq_zero_of_flat p k h0)
  obtain ⟨c', rfl⟩ := hsurj c
  have : a - c' * p ∈ (D.I j).ideal ⟨Õ, hÕ⟩ := by
    rw [← hker, RingHom.mem_ker, map_sub, map_mul, map_natCast, hc, sub_self]
  exact Submodule.mem_sup.2 ⟨_, this, c' * p, Ideal.mul_mem_left _ _ (Ideal.subset_span rfl),
    by ring⟩

/-- **Charts with Frobenius lifts from étale coordinates**: let `𝒲` be an affine open of the
lifting over a chart `W` of the divisor with equations `tⱼ`. If coordinates `sᵢ` containing the
`tⱼ` with `q j` are formally étale on `i⁻¹ 𝒲`, and the other `tⱼ` are units there, then `𝒲`
carries a chart with a Frobenius lift. -/
theorem exists_frobeniusLiftChart_of_formallyEtale {𝒲 : D.𝒱.Opens} (h𝒲 : IsAffineOpen 𝒲)
    {W : V.affineOpens} (h𝒲W : D.i ⁻¹ᵁ 𝒲 ≤ W) {t : ι → Γ(V, W)}
    (hideal : ∀ j, (D.J j).ideal W = Ideal.span {t j}) (q : ι → Prop) [DecidablePred q]
    (hunit : ∀ j, ¬q j → IsUnit ((V.presheaf.map (homOfLE h𝒲W).op).hom (t j)))
    [Algebra k Γ(V, D.i ⁻¹ᵁ 𝒲)] {m : ℕ} (s : Fin m → Γ(V, W)) (ε : {j // q j} ↪ Fin m)
    (hsε : ∀ j, s (ε j) = t j)
    (hét : (MvPolynomial.aeval (R := k) fun i =>
      (V.presheaf.map (homOfLE h𝒲W).op).hom (s i)).toRingHom.FormallyEtale) :
    ∃ C : D.FrobeniusLiftChart, C.𝒲 = 𝒲 := by
  set ρ := (V.presheaf.map (homOfLE h𝒲W).op).hom
  -- the lifted equations
  set π := (D.i.app 𝒲).hom
  have hred := D.isReductionModP_app 𝒲 h𝒲
  have hp2 := D.natCast_sq_eq_zero 𝒲
  have hJmap : ∀ j, ((D.I j).ideal ⟨𝒲, h𝒲⟩).map π = Ideal.span {ρ (t j)} := fun j => by
    rw [← D.ideal_J_eq_map j h𝒲,
      ← (D.J j).map_ideal (U := ⟨D.i ⁻¹ᵁ 𝒲, D.isAffineOpen_preimage h𝒲⟩) (V := W) h𝒲W,
      hideal j, Ideal.map_span, Set.image_singleton]
    rfl
  choose u hu hπu using fun j => (Ideal.mem_map_iff_of_surjective π hred.surjective).1
    ((hJmap j).symm ▸ Ideal.mem_span_singleton_self (ρ (t j)))
  have hIu : ∀ j, (D.I j).ideal ⟨𝒲, h𝒲⟩ = Ideal.span {u j} := fun j =>
    ideal_eq_span_singleton_of_le_sup_span hp2 (D.mem_ideal_sup_of_natCast_mul_mem j 𝒲 h𝒲)
      (hu j) (le_span_sup_span_of_map_le hred.surjective hred.ker_eq (by rw [hJmap, hπu]))
  -- the lifted coordinates
  let sL : Fin m → Γ(D.𝒱, 𝒲) := Function.extend ε (fun j => u j)
    fun i => Function.surjInv hred.surjective (ρ (s i))
  have hsLε : ∀ j, sL (ε j) = u j := ε.injective.extend_apply _ _
  have hπsL : ∀ i, π (sL i) = ρ (s i) := fun i => by
    by_cases h : ∃ j, ε j = i
    · obtain ⟨j, rfl⟩ := h
      rw [hsLε, hπu, ← hsε j]
    · simp only [sL, Function.extend_apply' _ _ _ h]
      exact Function.surjInv_eq hred.surjective _
  -- the Frobenius lift
  let : Algebra (TruncatedWittVector p 2 k) Γ(D.𝒱, 𝒲) := (D.sectionsRingHom 𝒲).toAlgebra
  obtain ⟨F₀, hF₀⟩ := exists_isFrobeniusLift_of_formallySmooth_truncatedWittVector
    (D.formallySmooth_sectionsRingHom 𝒲 h𝒲)
  obtain ⟨F, hF, hFs⟩ := exists_isFrobeniusLift_eq_pow_of_formallyEtale (k := k) hp2 π
    hred.surjective hred.ker_eq hF₀ sL (by simpa only [hπsL] using hét)
  let tL : ι → Γ(D.𝒱, 𝒲) := fun j => if q j then u j else 1
  refine ⟨FrobeniusLiftChart.mk 𝒲 h𝒲 tL (fun j => ?_) F hF (fun j => ?_), rfl⟩
  · simp only [tL]
    split_ifs with hj
    · exact hIu j
    · rw [hIu j, Ideal.span_singleton_one, Ideal.span_singleton_eq_top]
      exact isUnit_of_isUnit_map hp2 π hred.ker_eq hred.surjective
        (by rw [hπu]; exact hunit j hj)
  · simp only [tL]
    split_ifs with hj
    · rw [← hsLε ⟨j, hj⟩]
      exact hFs _
    · rw [map_one, one_pow]

/-- **Charts with Frobenius lifts exist**: every point of `V` lies in (the inverse image of) a
chart of the lifting carrying a Frobenius lift that fixes local equations of the lifted
divisor. -/
theorem exists_frobeniusLiftChart (x : V) : ∃ C : D.FrobeniusLiftChart, D.i x ∈ C.𝒲 := by
  classical
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  -- an affine open of the lifting through `i x`
  obtain ⟨-, ⟨Õ₀, hÕ₀, rfl⟩, hxÕ₀, -⟩ :=
    D.𝒱.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (D.i x)) isOpen_univ
  have hxÕ₀' : x ∈ D.i ⁻¹ᵁ Õ₀ := hxÕ₀
  -- a chart of the divisor inside it
  obtain ⟨W, t, hWO, hxW, hideal, -, -, hS⟩ :=
    exists_affineOpen_snc_chart_le f D.J D.hJ D.U D.hU hxÕ₀'
  let := MMP.Mori.sectionAlgebra f W
  have : Algebra.Smooth k Γ(V, W) := MMP.Flips.ResolutionInputs.smooth_sectionAlgebra f W.2
  set 𝔭 := W.2.primeIdealOf ⟨x, hxW⟩
  have hmem : ∀ a : Γ(V, W), x ∈ V.basicOpen a ↔ a ∉ 𝔭.asIdeal := fun a ↦ by
    rw [← PrimeSpectrum.mem_basicOpen a 𝔭, ← W.2.fromSpec_preimage_basicOpen a]
    change _ ↔ W.2.fromSpec.base 𝔭 ∈ V.basicOpen a
    rw [show W.2.fromSpec.base 𝔭 = x from W.2.fromSpec_primeIdealOf ⟨x, hxW⟩]
  -- étale coordinates near `x`
  obtain ⟨g, hg, m, s, ε, hsε, het⟩ := exists_etale_mvPolynomial_fin t hS 𝔭
  set g' : Γ(V, W) := g * ∏ j ∈ Finset.univ.filter (fun j => t j ∉ 𝔭.asIdeal), t j
  have hg' : g' ∉ 𝔭.asIdeal := 𝔭.asIdeal.primeCompl.mul_mem hg
    (Submonoid.prod_mem _ fun j hj => (Finset.mem_filter.1 hj).2)
  -- a basic open of `Õ₀` through `i x` over `D(g')`
  have hxL : D.i x ∈ D.liftOpen (V.basicOpen g') := ⟨x, (hmem g').2 hg', rfl⟩
  obtain ⟨a, haL, hxa⟩ := hÕ₀.exists_basicOpen_le ⟨D.i x, hxL⟩ hxÕ₀
  set 𝒲 : D.𝒱.Opens := D.𝒱.basicOpen a with h𝒲_def
  have h𝒲 : IsAffineOpen 𝒲 := hÕ₀.basicOpen a
  have h𝒲g' : D.i ⁻¹ᵁ 𝒲 ≤ V.basicOpen g' := by
    simpa only [D.preimage_liftOpen] using D.i.preimage_mono haL
  have h𝒲W : D.i ⁻¹ᵁ 𝒲 ≤ W := h𝒲g'.trans (V.basicOpen_le g')
  -- the reduction of the chart and its ring of functions
  set ρ : Γ(V, W) →+* Γ(V, D.i ⁻¹ᵁ 𝒲) := (V.presheaf.map (homOfLE h𝒲W).op).hom
  have hρg' : IsUnit (ρ g') := isUnit_map_of_le_basicOpen h𝒲W g' h𝒲g'
  rw [map_mul, map_prod] at hρg'
  have hρt : ∀ j, t j ∉ 𝔭.asIdeal → IsUnit (ρ (t j)) := fun j hj =>
    isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun j => ρ (t j))
      (Finset.mem_filter.2 ⟨Finset.mem_univ j, hj⟩)) (isUnit_of_mul_isUnit_right hρg')
  set a' : Γ(V, W) := V.presheaf.map (homOfLE hWO).op (D.i.app Õ₀ a)
  have ha' : D.i ⁻¹ᵁ 𝒲 = V.basicOpen a' := by
    have h := h𝒲W
    rw [h𝒲_def, Scheme.preimage_basicOpen] at h ⊢
    rw [Scheme.basicOpen_res]
    exact (inf_eq_right.2 h).symm
  let : Algebra Γ(V, W) Γ(V, D.i ⁻¹ᵁ 𝒲) := ρ.toAlgebra
  have : IsLocalization.Away a' Γ(V, D.i ⁻¹ᵁ 𝒲) :=
    W.2.isLocalization_of_eq_basicOpen a' (homOfLE h𝒲W) ha'
  let : Algebra k Γ(V, D.i ⁻¹ᵁ 𝒲) := (ρ.comp (algebraMap k Γ(V, W))).toAlgebra
  have : IsScalarTower k Γ(V, W) Γ(V, D.i ⁻¹ᵁ 𝒲) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨C, hC⟩ := D.exists_frobeniusLiftChart_of_formallyEtale h𝒲 h𝒲W hideal
    (fun j => t j ∈ 𝔭.asIdeal) hρt s ε hsε
    (formallyEtale_aeval_of_isLocalization (k := k) s g a' (isUnit_of_mul_isUnit_left hρg') het)
  exact ⟨C, hC ▸ hxa⟩

/-- **The local Frobenius splitting exists**: the charts with Frobenius lifts through every
point give the local data of the decomposition. -/
theorem nonempty_localFrobeniusSplitting : Nonempty D.LocalFrobeniusSplitting :=
  D.nonempty_localFrobeniusSplitting_of_forall_exists_chart D.exists_frobeniusLiftChart

end FrobeniusSplittingData

end MMP.DeRham
