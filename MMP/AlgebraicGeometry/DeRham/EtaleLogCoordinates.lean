module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Unramified.Finite
public import StacksFrontier.RingTheory.DeRham.Cartier.Coordinates

/-!
# Étale-local coordinates and Frobenius coordinates along étale maps

Two inputs to the logarithmic inverse Cartier isomorphism on a smooth variety with a simple normal
crossing divisor.

**Étale-local coordinates.** Let `B` be a smooth algebra over a field `k` and `t : ι → B` a
family such that at every prime `𝔭` the differentials `1 ⊗ dtⱼ` of the `tⱼ ∈ 𝔭` are linearly
independent in `κ(𝔭) ⊗[B] Ω[B⁄k]` (the divisor `∑ⱼ V(tⱼ)` has simple normal crossings). Complete
them by differentials `1 ⊗ dbᵢ` to a basis of `κ(𝔭) ⊗[B] Ω[B⁄k]`. Then the `dtⱼ, dbᵢ` form a basis
of the free module `Ω[B_𝔭⁄k]` (Nakayama), so the map `k[xⱼ, yᵢ] → B` sending `xⱼ ↦ tⱼ`,
`yᵢ ↦ bᵢ` induces an isomorphism `B_𝔭 ⊗ Ω[k[x, y]⁄k] ≅ Ω[B_𝔭⁄k]`. Since `B_𝔭` is formally smooth
over `k`, the Jacobi–Zariski sequence shows that `B_𝔭` is formally étale over `k[x, y]`, and the
étale locus being open, `B_f` is étale over `k[x, y]` for some `f ∉ 𝔭`.

**Frobenius coordinates along étale maps.** Let `A → B` be étale, with `A` of characteristic `p`.
The relative Frobenius `A ⊗[A, F] B → B`, `a ⊗ b ↦ a bᵖ`, is a map of étale `A`-algebras, hence
étale, and the Frobenius of either side factors through it. An étale map `C → B` with a map
`ψ : B → C` such that both composites are the Frobenius is bijective: it is faithfully flat, since
`ψ` splits it on spectra; and the diagonal idempotent `e ∈ B ⊗[C] B` of the unramified map
satisfies `eᵖ = 1`, so `b ⊗ 1 = 1 ⊗ b` for all `b`, whence `B → B ⊗[C] B` is bijective and so is
`C → B` by faithfully flat descent. Base changing the Frobenius basis `t^α` of `A` along `A → B`
and composing with the relative Frobenius shows that the images of Frobenius coordinates of `A`
are Frobenius coordinates of `B`.

## Main results

* `MMP.DeRham.exists_etale_aeval_of_residueField_basis`: if `1 ⊗ dsᵢ` is a basis of
  `κ(𝔭) ⊗[B] Ω[B⁄k]`, then `k[xᵢ] → B_f`, `xᵢ ↦ sᵢ`, is étale for some `f ∉ 𝔭`.
* `MMP.DeRham.exists_etale_mvPolynomial`, `MMP.DeRham.exists_etale_mvPolynomial_fin`:
  **étale-local coordinates** `k[x] → B_f` along a simple normal crossing family.
* `MMP.DeRham.formallyEtale_of_mapBaseChange_bijective`: the Jacobian criterion, `T` formally
  smooth over `R` and `T ⊗[S] Ω[S⁄R] ≅ Ω[T⁄R]` imply `T` formally étale over `S`.
* `MMP.DeRham.bijective_algebraMap_of_frobenius`: an étale Frobenius-isomorphism is bijective.
* `MMP.DeRham.exists_bijective_relativeFrobenius`: the relative Frobenius of an étale map is an
  isomorphism.
* `MMP.DeRham.isFrobeniusCoordinates_of_etale`: **Frobenius coordinates transfer along étale
  maps**.

## Implementation notes

The Frobenius twist `A ⊗[A, F] B` needs `A` as an algebra over itself through the Frobenius,
which clashes with the identity algebra structure. The relative Frobenius and the transfer of
coordinates are therefore proved for abstract `A'`, `B'` with ring isomorphisms `A' ≃ A`,
`B ≃ B'` (`exists_bijective_relativeFrobenius`, `isFrobeniusCoordinates_of_twist`), and
specialised in `isFrobeniusCoordinates_of_etale` by passing the twisted structures explicitly.
No perfectness of `A` is needed.

## References

* P. Deligne, L. Illusie, *Relèvements modulo p² et décomposition du complexe de de Rham*,
  Invent. Math. 89 (1987), §4.
-/

@[expose] public section

universe u

open TensorProduct KaehlerDifferential KaehlerDifferential.Cartier

namespace MMP.DeRham

section EtaleCoordinates

variable {k B : Type*} [Field k] [CommRing B] [Algebra k B]

/-- The differentials `1 ⊗ db`, `b ∈ B`, span `K ⊗[B] Ω[B⁄k]` over any `B`-algebra `K`. -/
theorem span_tmul_D_eq_top (K : Type*) [CommRing K] [Algebra B K] :
    Submodule.span K (Set.range fun b : B ↦ (1 : K) ⊗ₜ[B] D k B b) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun x ↦ ?_
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul c ω =>
    have hω : ω ∈ Submodule.span B (Set.range (D k B)) := by
      rw [span_range_derivation]
      trivial
    induction hω using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨b, rfl⟩ := h
      rw [show c ⊗ₜ[B] D k B b = c • ((1 : K) ⊗ₜ[B] D k B b) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [tmul_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [TensorProduct.tmul_smul, ← algebraMap_smul K a]
      exact Submodule.smul_mem _ _ hx

/-- **Jacobian criterion for étaleness.** If `T` is formally smooth over `R` and
`T ⊗[S] Ω[S⁄R] → Ω[T⁄R]` is bijective, then `T` is formally étale over `S`. -/
theorem formallyEtale_of_mapBaseChange_bijective {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra.FormallySmooth R T] (h : Function.Bijective (mapBaseChange R S T)) :
    Algebra.FormallyEtale S T := by
  rw [Algebra.formallyEtale_iff]
  constructor
  · refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    obtain ⟨y, rfl⟩ := KaehlerDifferential.map_surjective R S T x
    exact (KaehlerDifferential.exact_mapBaseChange_map R S T y).2 (h.2 y)
  · refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    have h0 : Algebra.H1Cotangent.δ R S T x = 0 :=
      h.1 (((Algebra.H1Cotangent.exact_δ_mapBaseChange R S T _).2 ⟨x, rfl⟩).trans
        (map_zero _).symm)
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ R S T x).1 h0
    rw [Subsingleton.elim y 0, map_zero]

variable [Algebra.Smooth k B] {ι : Type*} (t : ι → B)

/-- Given the `t j` with `t j ∈ 𝔭` whose differentials are independent in `κ(𝔭) ⊗ Ω[B⁄k]`,
there are `b₁, …, bₘ ∈ B` completing them to a basis `1 ⊗ dtⱼ, 1 ⊗ dbᵢ` of `κ(𝔭) ⊗ Ω[B⁄k]`. -/
theorem exists_completion_basis (𝔭 : PrimeSpectrum B)
    (h𝔭 : LinearIndependent 𝔭.asIdeal.ResidueField
      (fun j : {j : ι // t j ∈ 𝔭.asIdeal} ↦
        ((1 : 𝔭.asIdeal.ResidueField) ⊗ₜ[B] D k B (t j) :
          𝔭.asIdeal.ResidueField ⊗[B] Ω[B⁄k]))) :
    ∃ (m : ℕ) (b : Fin m → B),
      LinearIndependent 𝔭.asIdeal.ResidueField
        (fun i ↦ (1 : 𝔭.asIdeal.ResidueField) ⊗ₜ[B]
          D k B (Sum.elim (fun j : {j : ι // t j ∈ 𝔭.asIdeal} ↦ t j) b i)) ∧
      Submodule.span 𝔭.asIdeal.ResidueField (Set.range fun i ↦
        (1 : 𝔭.asIdeal.ResidueField) ⊗ₜ[B]
          D k B (Sum.elim (fun j : {j : ι // t j ∈ 𝔭.asIdeal} ↦ t j) b i)) = ⊤ := by
  set κ := 𝔭.asIdeal.ResidueField
  set J := {j : ι // t j ∈ 𝔭.asIdeal}
  let v : J ⊕ B → κ ⊗[B] Ω[B⁄k] :=
    Sum.elim (fun j ↦ (1 : κ) ⊗ₜ[B] D k B (t j)) (fun b ↦ (1 : κ) ⊗ₜ[B] D k B b)
  have hs : LinearIndepOn κ v (Set.range Sum.inl) :=
    (linearIndepOn_range_iff Sum.inl_injective v).2 h𝔭
  obtain ⟨E, -, hsE, hspan, hE⟩ := exists_linearIndepOn_extension hs (Set.subset_univ _)
  have hEfin : Finite E := hE.finite
  let F := {b : B // Sum.inr b ∈ E}
  have : Finite F := Finite.of_injective (fun b : F ↦ (⟨Sum.inr b.1, b.2⟩ : E))
    fun b c h ↦ Subtype.ext (Sum.inr_injective (congrArg Subtype.val h))
  let e : F ≃ Fin (Nat.card F) := Finite.equivFin F
  let b : Fin (Nat.card F) → B := fun i ↦ (e.symm i).1
  let g : J ⊕ Fin (Nat.card F) → E := fun i ↦ match i with
    | Sum.inl j => ⟨Sum.inl j, hsE ⟨j, rfl⟩⟩
    | Sum.inr i => ⟨Sum.inr (b i), (e.symm i).2⟩
  have hg : Function.Injective g := by
    rintro (j | i) (j' | i') h <;> simp only [g, Subtype.mk.injEq, reduceCtorEq,
      Sum.inl.injEq, Sum.inr.injEq] at h
    · rw [h]
    · rw [e.symm.injective (Subtype.ext h)]
  have hg' : Function.Surjective g := by
    rintro ⟨j | c, hc⟩
    · exact ⟨Sum.inl j, rfl⟩
    · exact ⟨Sum.inr (e ⟨c, hc⟩), by simp [g, b]⟩
  have hvg : (fun i ↦ (1 : κ) ⊗ₜ[B] D k B (Sum.elim (fun j : J ↦ t j) b i)) =
      (fun x : E ↦ v x) ∘ g := by
    funext i
    rcases i with j | i <;> rfl
  refine ⟨Nat.card F, b, ?_, ?_⟩
  · rw [hvg]
    exact hE.comp g hg
  · rw [hvg, Set.range_comp, hg'.range_eq, Set.image_univ, eq_top_iff,
      ← span_tmul_D_eq_top (k := k) κ]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨c, rfl⟩
    have : v (Sum.inr c) ∈ Submodule.span κ (v '' E) := hspan ⟨Sum.inr c, trivial, rfl⟩
    simpa [Set.image_eq_range, v] using this

/-- If the `1 ⊗ dsᵢ` form a basis of `κ(𝔭) ⊗[B] Ω[B⁄k]`, then the `dsᵢ` form a basis of
`Ω[B_𝔭⁄k]`. -/
theorem linearCombination_D_bijective_of_residueField (𝔭 : Ideal B) [𝔭.IsPrime]
    {σ : Type*} (s : σ → B)
    (hli : LinearIndependent 𝔭.ResidueField
      (fun i ↦ (1 : 𝔭.ResidueField) ⊗ₜ[B] D k B (s i)))
    (hsp : Submodule.span 𝔭.ResidueField (Set.range fun i ↦
      (1 : 𝔭.ResidueField) ⊗ₜ[B] D k B (s i)) = ⊤) :
    Function.Bijective (Finsupp.linearCombination (Localization.AtPrime 𝔭)
      fun i ↦ D k (Localization.AtPrime 𝔭) (algebraMap B (Localization.AtPrime 𝔭) (s i))) := by
  set T := Localization.AtPrime 𝔭
  set κ := 𝔭.ResidueField
  have : Algebra.FormallySmooth k T := Algebra.FormallySmooth.comp k B T
  let eT := tensorKaehlerEquivOfFormallyEtale k B T
  have : Module.Finite T Ω[T⁄k] := Module.Finite.equiv eT
  let e : κ ⊗[T] Ω[T⁄k] ≃ₗ[κ] κ ⊗[B] Ω[B⁄k] :=
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl κ κ) eT.symm).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange B T κ κ Ω[B⁄k])
  have he : ∀ i, e ((1 : κ) ⊗ₜ[T] D k T (algebraMap B T (s i))) =
      (1 : κ) ⊗ₜ[B] D k B (s i) := by
    intro i
    simp [e, eT, tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
  have hv : (fun i ↦ (1 : κ) ⊗ₜ[B] D k B (s i)) =
      e ∘ (TensorProduct.mk T κ Ω[T⁄k] 1 ∘ fun i ↦ D k T (algebraMap B T (s i))) :=
    funext fun i ↦ (he i).symm
  refine Module.IsLocalRing.linearCombination_bijective_of_flat _ ⟨?_, ?_⟩
  · rw [hv] at hli
    exact LinearIndependent.of_comp _ hli
  · intro x
    have hx : e x ∈ Submodule.span κ (Set.range fun i ↦ (1 : κ) ⊗ₜ[B] D k B (s i)) :=
      hsp ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hx
    refine ⟨c, e.injective ?_⟩
    rw [← hc, Finsupp.linearCombination_apply, map_finsuppSum]
    refine Finsupp.sum_congr fun i _ ↦ ?_
    rw [map_smul]
    exact congrArg (c i • ·) (he i)

/-- **Étale coordinates from a residual basis of differentials.** Let `B` be smooth over a field
`k`, `𝔭` a prime of `B` and `s : σ → B` a finite family whose differentials `1 ⊗ dsᵢ` form a basis
of `κ(𝔭) ⊗[B] Ω[B⁄k]`. Then on some `D(f) ∋ 𝔭` the map `k[xᵢ] → B_f`, `xᵢ ↦ sᵢ`, is étale. -/
theorem exists_etale_aeval_of_residueField_basis (𝔭 : PrimeSpectrum B) {σ : Type*} [Finite σ]
    (s : σ → B)
    (hli : LinearIndependent 𝔭.asIdeal.ResidueField
      (fun i ↦ (1 : 𝔭.asIdeal.ResidueField) ⊗ₜ[B] D k B (s i)))
    (hsp : Submodule.span 𝔭.asIdeal.ResidueField (Set.range fun i ↦
      (1 : 𝔭.asIdeal.ResidueField) ⊗ₜ[B] D k B (s i)) = ⊤) :
    ∃ f ∉ 𝔭.asIdeal, (MvPolynomial.aeval (R := k) fun i ↦
      algebraMap B (Localization.Away f) (s i)).toRingHom.Etale := by
  let P := MvPolynomial σ k
  let _ : Algebra P B := (MvPolynomial.aeval s).toAlgebra
  have : IsScalarTower k P B :=
    IsScalarTower.of_algebraMap_eq fun x ↦ ((MvPolynomial.aeval s).commutes x).symm
  have hPB : ∀ i, algebraMap P B (MvPolynomial.X i) = s i := fun i ↦ MvPolynomial.aeval_X s i
  set T := Localization.AtPrime 𝔭.asIdeal
  have hbij := linearCombination_D_bijective_of_residueField 𝔭.asIdeal s hli hsp
  have : Algebra.FormallySmooth k T := Algebra.FormallySmooth.comp k B T
  let bT := Algebra.TensorProduct.basis T (mvPolynomialBasis k σ)
  have hcomp : mapBaseChange k P T ∘ₗ bT.repr.symm.toLinearMap =
      Finsupp.linearCombination T fun i ↦ D k T (algebraMap B T (s i)) := by
    refine Finsupp.lhom_ext' fun i ↦ LinearMap.ext_ring ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      Module.Basis.repr_symm_apply, Finsupp.lsingle_apply, Finsupp.linearCombination_single,
      one_smul, bT,
      Algebra.TensorProduct.basis_apply, mvPolynomialBasis_apply]
    rw [mapBaseChange_tmul, one_smul, map_D, IsScalarTower.algebraMap_apply P B T, hPB]
  have hmb : Function.Bijective (mapBaseChange k P T) := by
    have : ⇑(mapBaseChange k P T) =
        (Finsupp.linearCombination T fun i ↦ D k T (algebraMap B T (s i))) ∘ bT.repr := by
      rw [← hcomp]
      funext x
      simp
    rw [this]
    exact hbij.comp bT.repr.bijective
  have : Algebra.FormallyEtale P T := formallyEtale_of_mapBaseChange_bijective hmb
  have : Algebra.FinitePresentation P B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation k P B
  obtain ⟨f, hf, het⟩ := Algebra.exists_etale_of_isEtaleAt (R := P) 𝔭.asIdeal
  refine ⟨f, hf, ?_⟩
  have : (MvPolynomial.aeval (R := k) fun i : σ ↦
      algebraMap B (Localization.Away f) (s i)).toRingHom =
      algebraMap P (Localization.Away f) := by
    refine MvPolynomial.ringHom_ext (fun x ↦ ?_) (fun i ↦ ?_)
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C]
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    · simp [IsScalarTower.algebraMap_apply P B (Localization.Away f), hPB]
  rwa [this, RingHom.etale_algebraMap]

/-- **Étale-local coordinates along a simple normal crossing family.** Let `B` be smooth over a
field `k` and `t : ι → B` such that at every prime `𝔭` the differentials of the `tⱼ ∈ 𝔭` are
independent in `κ(𝔭) ⊗ Ω[B⁄k]`. Then every prime `𝔭` has a neighbourhood `D(f)` and
`b₁, …, bₘ ∈ B` such that the `k`-algebra map `k[xⱼ, yᵢ] → B_f`, `xⱼ ↦ tⱼ` (for `tⱼ ∈ 𝔭`),
`yᵢ ↦ bᵢ`, is étale. -/
theorem exists_etale_mvPolynomial
    (hS : ∀ 𝔭 : PrimeSpectrum B,
      LinearIndependent 𝔭.asIdeal.ResidueField
        (fun j : {j : ι // t j ∈ 𝔭.asIdeal} ↦
          ((1 : 𝔭.asIdeal.ResidueField) ⊗ₜ[B] D k B (t j) :
            𝔭.asIdeal.ResidueField ⊗[B] Ω[B⁄k])))
    (𝔭 : PrimeSpectrum B) :
    ∃ f ∉ 𝔭.asIdeal, ∃ (m : ℕ) (b : Fin m → B),
      (MvPolynomial.aeval (R := k) fun i : {j : ι // t j ∈ 𝔭.asIdeal} ⊕ Fin m ↦
        algebraMap B (Localization.Away f)
          (Sum.elim (fun j : {j : ι // t j ∈ 𝔭.asIdeal} ↦ t j) b i)).toRingHom.Etale := by
  obtain ⟨m, b, hli, hsp⟩ := exists_completion_basis t 𝔭 (hS 𝔭)
  have : Finite {j : ι // t j ∈ 𝔭.asIdeal} := (hS 𝔭).finite
  obtain ⟨f, hf, het⟩ := exists_etale_aeval_of_residueField_basis 𝔭 _ hli hsp
  exact ⟨f, hf, m, b, het⟩

/-- **Étale-local coordinates, enumerated.** The form of `exists_etale_mvPolynomial` with the
coordinates indexed by `Fin n`: near every prime `𝔭` there are `s₁, …, sₙ ∈ B`, among them every
`tⱼ ∈ 𝔭` (through an injection `j ↦ ε j`), such that `k[x₁, …, xₙ] → B_f`, `xᵢ ↦ sᵢ`, is
étale. -/
theorem exists_etale_mvPolynomial_fin
    (hS : ∀ 𝔭 : PrimeSpectrum B,
      LinearIndependent 𝔭.asIdeal.ResidueField
        (fun j : {j : ι // t j ∈ 𝔭.asIdeal} ↦
          ((1 : 𝔭.asIdeal.ResidueField) ⊗ₜ[B] D k B (t j) :
            𝔭.asIdeal.ResidueField ⊗[B] Ω[B⁄k])))
    (𝔭 : PrimeSpectrum B) :
    ∃ f ∉ 𝔭.asIdeal, ∃ (n : ℕ) (s : Fin n → B) (ε : {j : ι // t j ∈ 𝔭.asIdeal} ↪ Fin n),
      (∀ j, s (ε j) = t j) ∧
      (MvPolynomial.aeval (R := k) fun i : Fin n ↦
        algebraMap B (Localization.Away f) (s i)).toRingHom.Etale := by
  obtain ⟨m, b, hli, hsp⟩ := exists_completion_basis t 𝔭 (hS 𝔭)
  set J := {j : ι // t j ∈ 𝔭.asIdeal}
  have : Finite J := (hS 𝔭).finite
  have : Fintype J := Fintype.ofFinite J
  let eσ : J ⊕ Fin m ≃ Fin (Fintype.card (J ⊕ Fin m)) := Fintype.equivFin _
  let s₀ : J ⊕ Fin m → B := Sum.elim (fun j : J ↦ t j) b
  have hli' := hli.comp eσ.symm eσ.symm.injective
  have hsp' : Submodule.span 𝔭.asIdeal.ResidueField (Set.range fun i ↦
      (1 : 𝔭.asIdeal.ResidueField) ⊗ₜ[B] D k B ((s₀ ∘ eσ.symm) i)) = ⊤ := by
    rw [← hsp]
    congr 1
    exact eσ.symm.surjective.range_comp (fun i ↦ (1 : 𝔭.asIdeal.ResidueField) ⊗ₜ[B] D k B (s₀ i))
  obtain ⟨f, hf, het⟩ := exists_etale_aeval_of_residueField_basis 𝔭 _ hli' hsp'
  exact ⟨f, hf, _, s₀ ∘ eσ.symm, ⟨eσ ∘ Sum.inl, eσ.injective.comp Sum.inl_injective⟩,
    fun j ↦ by simp [s₀], het⟩

end EtaleCoordinates

section Frobenius

/-- In a commutative ring in which the prime `p` vanishes, `(x + y)ᵖ = xᵖ + yᵖ`. -/
theorem add_pow_of_natCast_eq_zero {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime)
    (h : (p : R) = 0) (x y : R) : (x + y) ^ p = x ^ p + y ^ p := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp x y
  simp [hr, h]

/-- **An étale map that is a Frobenius-isomorphism is an isomorphism.** Let `C → B` be étale, `p`
a prime vanishing in `C`, and `ψ : B → C` a ring map such that both composites `C → B → C` and
`B → C → B` are the Frobenius `x ↦ xᵖ`. Then `C → B` is bijective. -/
theorem bijective_algebraMap_of_frobenius {C B : Type*} [CommRing C] [CommRing B] [Algebra C B]
    [Algebra.Etale C B] {p : ℕ} (hp : p.Prime) (hpC : (p : C) = 0) (ψ : B →+* C)
    (h₁ : ∀ b, algebraMap C B (ψ b) = b ^ p) (h₂ : ∀ c, ψ (algebraMap C B c) = c ^ p) :
    Function.Bijective (algebraMap C B) := by
  have hpB : (p : B) = 0 := by rw [← map_natCast (algebraMap C B), hpC, map_zero]
  have hff : Module.FaithfullyFlat C B := by
    refine .of_comap_surjective fun q ↦ ⟨PrimeSpectrum.comap ψ q, PrimeSpectrum.ext ?_⟩
    ext x
    change ψ (algebraMap C B x) ∈ q.asIdeal ↔ x ∈ q.asIdeal
    rw [h₂]
    exact q.2.pow_mem_iff_mem p hp.pos
  -- Every `x ∈ B ⊗[C] B` satisfies `xᵖ = 1 ⊗ (μ x)ᵖ`, `μ` the multiplication.
  have hpBB : (p : B ⊗[C] B) = 0 := by
    rw [← map_natCast (algebraMap B (B ⊗[C] B)), hpB, map_zero]
  have hpow : ∀ x : B ⊗[C] B, x ^ p = 1 ⊗ₜ[C] ((Algebra.TensorProduct.lmul' C x) ^ p) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp [zero_pow hp.ne_zero]
    | add x y hx hy =>
      rw [add_pow_of_natCast_eq_zero hp hpBB, hx, hy, map_add,
        add_pow_of_natCast_eq_zero hp hpB, tmul_add]
    | tmul a b =>
      rw [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.lmul'_apply_tmul, mul_pow,
        ← h₁ a, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, smul_mul_assoc,
        one_mul]
  obtain ⟨e, he, he1⟩ := Algebra.FormallyUnramified.iff_exists_tensorProduct.1
    (inferInstance : Algebra.FormallyUnramified C B)
  have heu : IsUnit e := by
    refine IsUnit.of_pow_eq_one (n := p) ?_ hp.ne_zero
    rw [hpow, he1, one_pow]
    rfl
  have hcomm : ∀ s : B, (1 : B) ⊗ₜ[C] s = s ⊗ₜ[C] 1 := fun s ↦
    sub_eq_zero.1 (heu.mul_left_eq_zero.1 (he s))
  refine Module.FaithfullyFlat.bijective_of_tensorProduct (S := B) ⟨fun x y hxy ↦ ?_, fun x ↦ ?_⟩
  · simpa [Algebra.TensorProduct.algebraMap_apply] using
      congrArg (Algebra.TensorProduct.lmul' C (S := B)) hxy
  · induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add _ _ _⟩
    | tmul a b =>
      refine ⟨a * b, ?_⟩
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      calc (a * b) ⊗ₜ[C] (1 : B) = (a ⊗ₜ[C] (1 : B)) * (b ⊗ₜ[C] (1 : B)) := by
            rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
        _ = (a ⊗ₜ[C] (1 : B)) * ((1 : B) ⊗ₜ[C] b) := by rw [hcomm]
        _ = a ⊗ₜ[C] b := by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- **The relative Frobenius of an étale map is an isomorphism.** Let `A → B` be étale with the
prime `p` vanishing in `A`. Let `A'` be `A` viewed as an `A`-algebra through the Frobenius, given
abstractly by a ring isomorphism `g : A' ≃ A` with `g (a • 1) = aᵖ`, and let `B'` be `B` viewed as
an `A'`-algebra, given by `e : B ≃ B'` compatible with `g`. Then the relative Frobenius
`A' ⊗[A] B → B'`, `a' ⊗ b ↦ a' · bᵖ`, is an isomorphism. -/
theorem exists_bijective_relativeFrobenius {A A' B B' : Type*} [CommRing A] [CommRing A']
    [CommRing B] [CommRing B'] [Algebra A B] [Algebra.Etale A B] [Algebra A A'] [Algebra A' B']
    [Algebra A B'] [IsScalarTower A A' B'] [Algebra.Etale A' B'] {p : ℕ} (hp : p.Prime)
    (hpA : (p : A) = 0) (g : A' ≃+* A) (hg : ∀ a, g (algebraMap A A' a) = a ^ p)
    (e : B ≃+* B') (he : ∀ a', e.symm (algebraMap A' B' a') = algebraMap A B (g a')) :
    ∃ Φ : A' ⊗[A] B →ₐ[A'] B', (∀ a' b, Φ (a' ⊗ₜ b) = algebraMap A' B' a' * e (b ^ p)) ∧
      Function.Bijective Φ := by
  have hpB : (p : B) = 0 := by rw [← map_natCast (algebraMap A B), hpA, map_zero]
  let F : B →+* B :=
    { toFun := fun b ↦ b ^ p
      map_one' := one_pow p
      map_mul' := fun x y ↦ mul_pow x y p
      map_zero' := zero_pow hp.ne_zero
      map_add' := add_pow_of_natCast_eq_zero hp hpB }
  let f : B →ₐ[A] B' :=
    { e.toRingHom.comp F with
      commutes' := fun a ↦ by
        change e (algebraMap A B a ^ p) = algebraMap A B' a
        rw [← map_pow, ← hg, ← he, RingEquiv.apply_symm_apply,
          ← IsScalarTower.algebraMap_apply] }
  have hf : ∀ b, f b = e (b ^ p) := fun _ ↦ rfl
  let Φ : A' ⊗[A] B →ₐ[A'] B' :=
    Algebra.TensorProduct.lift (Algebra.ofId A' B') f fun _ _ ↦ Commute.all _ _
  have hΦ : ∀ a' b, Φ (a' ⊗ₜ b) = algebraMap A' B' a' * e (b ^ p) := fun a' b ↦ by
    rw [Algebra.TensorProduct.lift_tmul, hf]
    rfl
  refine ⟨Φ, hΦ, ?_⟩
  let _ : Algebra (A' ⊗[A] B) B' := Φ.toRingHom.toAlgebra
  have : IsScalarTower A' (A' ⊗[A] B) B' :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (Φ.commutes x).symm
  have : Algebra.Etale (A' ⊗[A] B) B' := Algebra.Etale.of_restrictScalars A' _ B'
  have hpC : (p : A' ⊗[A] B) = 0 := by
    rw [← map_natCast (algebraMap A (A' ⊗[A] B)), hpA, map_zero]
  let ψ : B' →+* A' ⊗[A] B :=
    (Algebra.TensorProduct.includeRight : B →ₐ[A] A' ⊗[A] B).toRingHom.comp e.symm.toRingHom
  have hψ : ∀ b', ψ b' = 1 ⊗ₜ e.symm b' := fun _ ↦ rfl
  refine bijective_algebraMap_of_frobenius hp hpC ψ (fun b' ↦ ?_) (fun c ↦ ?_)
  · change Φ (ψ b') = b' ^ p
    rw [hψ, hΦ, map_one, one_mul, map_pow, RingEquiv.apply_symm_apply]
  · change ψ (Φ c) = c ^ p
    induction c using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, zero_pow hp.ne_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy, add_pow_of_natCast_eq_zero hp hpC]
    | tmul a' b =>
      have hga : algebraMap A A' (g a') = a' ^ p :=
        g.injective (by rw [hg, map_pow])
      rw [hΦ, hψ, map_mul, he, RingEquiv.symm_apply_apply, Algebra.TensorProduct.tmul_pow,
        Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, ← TensorProduct.smul_tmul,
        Algebra.smul_def, mul_one, hga]

/-- Frobenius coordinates transfer along a map `A → B` whose relative Frobenius is an
isomorphism, in the abstract form of `exists_bijective_relativeFrobenius`. -/
theorem isFrobeniusCoordinates_of_twist {A A' B B' : Type*} [CommRing A] [CommRing A']
    [CommRing B] [CommRing B'] [Algebra A B] [Algebra.Etale A B] [instAA' : Algebra A A']
    [instA'B' : Algebra A' B'] [instAB' : Algebra A B'] [tower : IsScalarTower A A' B']
    [etale : Algebra.Etale A' B'] {p : ℕ} (hp : p.Prime) (hpA : (p : A) = 0) (g : A' ≃+* A)
    (hg : ∀ a, g (algebraMap A A' a) = a ^ p) (e : B ≃+* B')
    (he : ∀ a', e.symm (algebraMap A' B' a') = algebraMap A B (g a')) {n : ℕ} {t : Fin n → A}
    (ht : IsFrobeniusCoordinates p A t) :
    IsFrobeniusCoordinates p B (algebraMap A B ∘ t) := by
  classical
  obtain ⟨Φ, hΦ, hbij⟩ := exists_bijective_relativeFrobenius hp hpA g hg e he
  have hpB : (p : B) = 0 := by rw [← map_natCast (algebraMap A B), hpA, map_zero]
  let m : (Fin n → Fin p) → A := fun α ↦ monomial t fun j ↦ (α j : ℕ)
  have hmono : ∀ α : Fin n → Fin p, monomial (algebraMap A B ∘ t) (fun j ↦ (α j : ℕ)) =
      algebraMap A B (m α) := fun α ↦ by
    simp [m, monomial, map_prod, map_pow]
  let LA : ((Fin n → Fin p) → A) →ₗ[A] A' := Fintype.linearCombination A fun α ↦ g.symm (m α)
  have hLA : ∀ c, g (LA c) = ∑ α, c α ^ p * m α := fun c ↦ by
    rw [Fintype.linearCombination_apply, map_sum]
    refine Finset.sum_congr rfl fun α _ ↦ ?_
    rw [Algebra.smul_def, map_mul, hg, RingEquiv.apply_symm_apply]
  have hLAbij : Function.Bijective LA := by
    have : ⇑LA = g.symm ∘ fun c : (Fin n → Fin p) → A ↦ ∑ α, c α ^ p * m α :=
      funext fun c ↦ by rw [Function.comp_apply, ← hLA, RingEquiv.symm_apply_apply]
    rw [this]
    exact g.symm.bijective.comp ht
  let eLA := LinearEquiv.ofBijective LA hLAbij
  let Ψ : B ⊗[A] ((Fin n → Fin p) → A) → B := fun x ↦
    e.symm (Φ (TensorProduct.comm A B A' (LinearEquiv.lTensor B eLA x)))
  have hΨ : Function.Bijective Ψ :=
    e.symm.bijective.comp (hbij.comp ((TensorProduct.comm A B A').bijective.comp
      (LinearEquiv.lTensor B eLA).bijective))
  let ΦB : ((Fin n → Fin p) → B) → B := fun c ↦
    ∑ α, c α ^ p * monomial (algebraMap A B ∘ t) fun j ↦ (α j : ℕ)
  have key : ∀ x, ΦB (piScalarRight A A B (Fin n → Fin p) x) = Ψ x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp [ΦB, Ψ, zero_pow hp.ne_zero]
    | add x y hx hy =>
      rw [map_add, show Ψ (x + y) = Ψ x + Ψ y by simp only [Ψ, map_add], ← hx, ← hy]
      simp only [ΦB, Pi.add_apply, add_pow_of_natCast_eq_zero hp hpB, add_mul,
        Finset.sum_add_distrib]
    | tmul b c =>
      simp only [ΦB, Ψ, piScalarRight_apply, piScalarRightHom_tmul, LinearEquiv.lTensor_tmul,
        TensorProduct.comm_tmul, hΦ, map_mul, he, RingEquiv.symm_apply_apply, eLA,
        LinearEquiv.ofBijective_apply, hLA, map_sum, Finset.sum_mul, hmono]
      refine Finset.sum_congr rfl fun α _ ↦ ?_
      rw [map_pow, Algebra.smul_def, mul_pow]
      ring
  have : ΦB = Ψ ∘ (piScalarRight A A B (Fin n → Fin p)).symm := funext fun c ↦ by
    rw [Function.comp_apply, ← key, LinearEquiv.apply_symm_apply]
  change Function.Bijective ΦB
  rw [this]
  exact hΨ.comp (LinearEquiv.bijective _)

/-- **Frobenius coordinates transfer along étale maps.** If `A → B` is étale, `A` has
characteristic `p` and `t₁, …, tₙ` are Frobenius coordinates of `A`, then their images are
Frobenius coordinates of `B`. -/
theorem isFrobeniusCoordinates_of_etale {p : ℕ} [hp : Fact p.Prime] {A B : Type u} [CommRing A]
    [CommRing B] [CharP A p] [i₀ : Algebra A B] [het : Algebra.Etale A B] {n : ℕ}
    {t : Fin n → A} (ht : IsFrobeniusCoordinates p A t) :
    IsFrobeniusCoordinates p B (algebraMap A B ∘ t) := by
  let iF : Algebra A A := (frobenius A p).toAlgebra
  let iB : Algebra A B := ((algebraMap A B).comp (frobenius A p)).toAlgebra
  have tower : @IsScalarTower A A B iF.toSMul i₀.toSMul iB.toSMul :=
    @IsScalarTower.of_algebraMap_eq A A B _ _ _ iF i₀ iB fun _ ↦ rfl
  exact @isFrobeniusCoordinates_of_twist A A B B _ _ _ _ i₀ het iF i₀ iB tower
    het p hp.out (CharP.cast_eq_zero A p) (RingEquiv.refl A)
    (fun a ↦ frobenius_def p a) (RingEquiv.refl B) (fun _ ↦ rfl) n t ht

end Frobenius

end MMP.DeRham
