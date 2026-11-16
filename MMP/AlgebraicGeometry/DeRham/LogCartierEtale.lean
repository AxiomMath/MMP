module

public import MMP.AlgebraicGeometry.DeRham.LogCartierGlobal
public import MMP.AlgebraicGeometry.DeRham.EtaleLogCoordinates

/-!
# The logarithmic inverse Cartier theorem near a point with étale coordinates

Let `A` be a perfect ring of characteristic `p`, `A → B` a ring map, `t : ι → B` a finite family
and `L = B[1/∏ⱼ tⱼ]`. Let `𝔪` be a prime of `B` and suppose that on a neighbourhood `D(f₀)` of `𝔪`
there are `s₁, …, sₙ ∈ B`, among them every `tⱼ ∈ 𝔪`, such that `A[x₁, …, xₙ] → B_{f₀}`,
`xᵢ ↦ sᵢ`, is étale. Then on the smaller neighbourhood `D(f)`, `f = f₀ ∏_{tⱼ ∉ 𝔪} tⱼ`, the
logarithmic inverse Cartier theorem holds on `L[1/f]` up to powers of `f`
(`MMP.DeRham.exists_isLocalLogCartier_of_etale`).

On `B_f` the `sᵢ` are Frobenius coordinates (Frobenius coordinates transfer along étale maps)
and their differentials are a basis of `Ω[B_f⁄A]` (Kähler differentials of an étale algebra are
a base change). The ring `L[1/f]` is `B_f[1/∏_{tⱼ ∈ 𝔪} tⱼ]`, because the other `tⱼ` are units of
`B_f`, so the inverse Cartier theorem in coordinates applies.

## Main results

* `MMP.DeRham.exists_isLocalLogCartier_of_etale`: the local hypothesis of the gluing theorem
  `MMP.DeRham.exists_logInverseCartier_of_forall_isMaximal` near a point with étale coordinates.

## References

* [P. Deligne, L. Illusie, *Relèvements modulo p² et décomposition du complexe de de Rham*,
  Invent. Math. 89 (1987)][DeligneIllusie1987], §4.
-/

@[expose] public noncomputable section

open KaehlerDifferential KaehlerDifferential.Cartier

universe u

namespace MMP.DeRham

variable (p : ℕ) [hp : Fact p.Prime] {A B L : Type u} [CommRing A] [CharP A p] [PerfectRing A p]
  [CommRing B] [CommRing L] [Algebra A B] [Algebra A L] [Algebra B L] [IsScalarTower A B L]
  {ι : Type*} [Fintype ι] (t : ι → B) [IsLocalization.Away (∏ j, t j) L]

/-- If `S` is formally étale over `A[x₁, …, xₙ]`, the differentials of the `xᵢ` form a basis of
`Ω[S⁄A]`. -/
theorem exists_basis_D_of_formallyEtale_mvPolynomial {n : ℕ} (S : Type u) [CommRing S]
    [Algebra A S] [Algebra (MvPolynomial (Fin n) A) S] [IsScalarTower A (MvPolynomial (Fin n) A) S]
    [Algebra.FormallyEtale (MvPolynomial (Fin n) A) S] :
    ∃ b : Module.Basis (Fin n) S (Ω[S⁄A]),
      ∀ j, b j = D A S (algebraMap (MvPolynomial (Fin n) A) S (MvPolynomial.X j)) :=
  ⟨((mvPolynomialBasis A (Fin n)).baseChange S).map
      (tensorKaehlerEquivOfFormallyEtale A (MvPolynomial (Fin n) A) S), fun j ↦ by
    simp only [Module.Basis.map_apply, Module.Basis.baseChange_apply,
      tensorKaehlerEquivOfFormallyEtale_apply, mvPolynomialBasis_eq_D]
    rw [mapBaseChange_tmul, one_smul, map_D]⟩

omit [CharP A p] [PerfectRing A p] in
/-- If `Bf = B[1/f]` has Frobenius coordinates `xᵢ` whose differentials are a basis of `Ω[Bf⁄A]`,
among them every `tⱼ ∈ 𝔪`, and the other `tⱼ` are units of `Bf`, then the logarithmic inverse
Cartier theorem holds on `L[1/f]` up to powers of `f`. -/
theorem isLocalLogCartier_of_basis_D (𝔪 : Ideal B) [DecidablePred fun j ↦ t j ∈ 𝔪]
    {Bf : Type u} [CommRing Bf] [Algebra A Bf] [Algebra B Bf] [IsScalarTower A B Bf] (f : B)
    [IsLocalization.Away f Bf]
    [CharP (Localization.Away (algebraMap B L f)) p] {n : ℕ} {x : Fin n → Bf}
    {b : Module.Basis (Fin n) Bf (Ω[Bf⁄A])} (hb : ∀ j, b j = D A Bf (x j))
    (hF : IsFrobeniusCoordinates p Bf x) (ε : {j // t j ∈ 𝔪} ↪ Fin n)
    (hx : ∀ k, x (ε k) = algebraMap B Bf (t k)) {g : B} (hg : IsUnit (algebraMap B Bf g))
    (hprod : (∏ k : {j // t j ∈ 𝔪}, t k) * g = ∏ j, t j)
    (hpole : ∀ j, t j ∉ 𝔪 → IsUnit (algebraMap B Bf (t j))) :
    IsLocalLogCartier p A (Localization.Away (algebraMap B L f)) t f := by
  set L' := Localization.Away (algebraMap B L f)
  have hunit : IsUnit (algebraMap B L' f) := by
    rw [IsScalarTower.algebraMap_apply B L L']
    exact IsLocalization.Away.algebraMap_isUnit _
  let : Algebra Bf L' := (IsLocalization.Away.lift f hunit).toAlgebra
  have : IsScalarTower B Bf L' :=
    IsScalarTower.of_algebraMap_eq fun b ↦ (IsLocalization.Away.lift_eq f hunit b).symm
  have : IsScalarTower A Bf L' := IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A B Bf, ← IsScalarTower.algebraMap_apply B Bf L',
      IsScalarTower.algebraMap_apply A L L', IsScalarTower.algebraMap_apply A B L,
      ← IsScalarTower.algebraMap_apply B L L']
  have : IsLocalization.Away (algebraMap B Bf (∏ j, t j)) L' :=
    IsLocalization.Away.commutes Bf L L' f (∏ j, t j)
  set P : Finset (Fin n) := Finset.univ.map ε
  have h₁ : ∏ i ∈ P, x i = algebraMap B Bf (∏ k : {j // t j ∈ 𝔪}, t k) := by
    rw [Finset.prod_map, map_prod]
    exact Finset.prod_congr rfl fun k _ ↦ hx k
  have h₂ : (∏ i ∈ P, x i) * algebraMap B Bf g = algebraMap B Bf (∏ j, t j) := by
    rw [h₁, ← map_mul, hprod]
  have : IsLocalization.Away (∏ i ∈ P, x i) L' :=
    IsLocalization.Away.of_associated (r := algebraMap B Bf (∏ j, t j))
      ⟨hg.unit⁻¹, by rw [← h₂, mul_assoc, IsUnit.mul_val_inv, mul_one]⟩
  set bL := b.ofIsLocalizedModule L' (Submonoid.powers (∏ i ∈ P, x i))
    (KaehlerDifferential.map A A Bf L')
  have hbL : ∀ j, bL j = D A L' (algebraMap Bf L' (x j)) := fun j ↦ by
    rw [Module.Basis.ofIsLocalizedModule_apply, hb, KaehlerDifferential.map_D]
  have hcoord : ∀ (c : Bf) j, bL.repr (D A L' (algebraMap Bf L' c)) j ∈
      Set.range (algebraMap Bf L') := fun c j ↦
    ⟨b.repr (D A Bf c) j, by
      rw [← KaehlerDifferential.map_D A A Bf L', Module.Basis.ofIsLocalizedModule_repr_apply]⟩
  have hP : ∀ j ∈ P, IsUnit (algebraMap Bf L' (x j)) := fun j hj ↦
    isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem _ hj))
      (IsLocalization.Away.algebraMap_isUnit _)
  have htL : ∀ j, IsUnit (algebraMap B L' (t j)) := fun j ↦ by
    rw [IsScalarTower.algebraMap_apply B L L']
    exact (isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)))
      (IsLocalization.Away.algebraMap_isUnit (∏ j, t j))).map _
  refine isLocalLogCartier_of_coordinates p t (fun j : {j // t j ∈ 𝔪} ↦ algebraMap B Bf (t j))
    hP hbL (fun k ↦ ⟨ε k, Finset.mem_map_of_mem _ (Finset.mem_univ k), by simp only [hx]⟩)
    (fun i hi ↦ ?_) hcoord hF
    (isFrobeniusCoordinates_of_isLocalization_away p (∏ i ∈ P, x i) L' hF) f htL
    (fun j ↦ ?_) (fun k ↦ ⟨k, rfl⟩)
  · obtain ⟨k, -, rfl⟩ := Finset.mem_map.1 hi
    exact ⟨k, by simp only [hx]⟩
  · by_cases hj : t j ∈ 𝔪
    · exact Or.inr ⟨⟨j, hj⟩, rfl⟩
    · exact Or.inl (hpole j hj)

/-- **The local hypothesis near a point with étale coordinates.** If `A[x₁, …, xₙ] → B_{f₀}`,
`xᵢ ↦ sᵢ`, is étale near the prime `𝔪` and the `sᵢ` include every `tⱼ ∈ 𝔪`, then some `f ∉ 𝔪`
satisfies the logarithmic inverse Cartier theorem on `L[1/f]` up to powers of `f`. -/
theorem exists_isLocalLogCartier_of_etale (𝔪 : Ideal B) [𝔪.IsPrime] {f₀ : B} (hf₀ : f₀ ∉ 𝔪)
    {n : ℕ} (s : Fin n → B) (ε : {j // t j ∈ 𝔪} ↪ Fin n) (hs : ∀ j, s (ε j) = t j)
    (het : (MvPolynomial.aeval (R := A) fun i : Fin n ↦
      algebraMap B (Localization.Away f₀) (s i)).toRingHom.Etale) :
    ∃ f ∉ 𝔪, ∀ [CharP (Localization.Away (algebraMap B L f)) p],
      IsLocalLogCartier p A (Localization.Away (algebraMap B L f)) t f := by
  classical
  have hprodB : (∏ j ∈ Finset.univ.filter (fun j ↦ t j ∈ 𝔪), t j) *
      (∏ j ∈ Finset.univ.filter (fun j ↦ t j ∉ 𝔪), t j) = ∏ j, t j :=
    Finset.prod_filter_mul_prod_filter_not _ _ _
  have hJ : ∏ k : {j // t j ∈ 𝔪}, t k = ∏ j ∈ Finset.univ.filter (fun j ↦ t j ∈ 𝔪), t j :=
    (Finset.prod_subtype _ (fun j ↦ by simp) t).symm
  have hdvd : ∀ j, t j ∉ 𝔪 → t j ∣ ∏ j ∈ Finset.univ.filter (fun j ↦ t j ∉ 𝔪), t j :=
    fun j hj ↦ Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ j, hj⟩)
  have hg : ∏ j ∈ Finset.univ.filter (fun j ↦ t j ∉ 𝔪), t j ∉ 𝔪 := fun h ↦ by
    obtain ⟨j, hj, hjm⟩ := Ideal.IsPrime.prod_mem_iff.1 h
    exact (Finset.mem_filter.1 hj).2 hjm
  generalize ∏ j ∈ Finset.univ.filter (fun j ↦ t j ∉ 𝔪), t j = g at hprodB hdvd hg
  refine ⟨g * f₀, fun h ↦ (Ideal.IsPrime.mem_or_mem ‹_› h).elim hg hf₀, ?_⟩
  intro _
  set B₀ := Localization.Away f₀
  set Bf := Localization.Away (algebraMap B B₀ g)
  set R := MvPolynomial (Fin n) A
  let : Algebra R B₀ := (MvPolynomial.aeval (R := A) fun i : Fin n ↦
    algebraMap B B₀ (s i)).toRingHom.toAlgebra
  have : Algebra.Etale R B₀ := het.toAlgebra
  have : IsScalarTower A R B₀ := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change _ = MvPolynomial.aeval _ (MvPolynomial.C a)
    rw [MvPolynomial.aeval_C]
  have : IsScalarTower A R Bf := IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A B₀ Bf, IsScalarTower.algebraMap_apply A R B₀,
      ← IsScalarTower.algebraMap_apply R B₀ Bf]
  set x : Fin n → Bf := fun i ↦ algebraMap B Bf (s i)
  have hx : ∀ i, algebraMap R Bf (MvPolynomial.X i) = x i := fun i ↦ by
    rw [IsScalarTower.algebraMap_apply R B₀ Bf]
    change algebraMap B₀ Bf (MvPolynomial.aeval _ (MvPolynomial.X i)) = _
    rw [MvPolynomial.aeval_X, ← IsScalarTower.algebraMap_apply]
  have hF : IsFrobeniusCoordinates p Bf x := by
    convert isFrobeniusCoordinates_of_etale (A := R) (B := Bf) (t := MvPolynomial.X)
      (isFrobeniusCoordinates_mvPolynomial p A) using 1
    exact funext fun i ↦ (hx i).symm
  obtain ⟨b, hb⟩ := exists_basis_D_of_formallyEtale_mvPolynomial (A := A) (n := n) Bf
  exact isLocalLogCartier_of_basis_D p t 𝔪 (g * f₀) (fun j ↦ by rw [hb, hx]) hF ε
    (fun k ↦ by simp only [x, hs]) (IsLocalization.Away.isUnit_of_dvd _ (dvd_mul_right g f₀))
    (by rw [hJ, hprodB])
    fun j hj ↦ IsLocalization.Away.isUnit_of_dvd _ (dvd_mul_of_dvd_left (hdvd j hj) f₀)

end MMP.DeRham

end
