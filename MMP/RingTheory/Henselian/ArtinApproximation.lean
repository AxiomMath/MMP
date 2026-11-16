module

public import MMP.Attr
public import StacksFrontier.RingTheory.Henselian.Henselization.AlgebraicInCompletion
public import StacksFrontier.RingTheory.GRing.EssFiniteType

/-!
# Artin approximation in the henselization

Let `(A, 𝔪)` be a local ring essentially of finite type over a field, `Aʰ` its henselization and
`Â` its `𝔪`-adic completion. Every `A`-algebra map from a finitely presented `A`-algebra `R` to
`Â` is approximated modulo `𝔪ᴺ Â`, for every `N`, by an `A`-algebra map `R → Aʰ`.

## Main results

* `MMP.Resolution.Bridges.exists_algHom_henselization_approx`: the approximation theorem.

## Implementation notes

* The henselization is any `IsLocalRing.IsHenselization A (ResidueField A) Aʰ`, and `Aʰ → Â` is
  the canonical map `IsLocalRing.henselizationToAdicCompletion`.
* `A` is a Noetherian G-ring: a field is a G-ring and the property passes to essentially finite
  type algebras. The approximation is then Stacks Tag 07QZ, with the étale solution pushed into
  `Aʰ` by the universal property of the henselization (a map from an étale algebra into a
  henselian local ring is determined by its residue point).
-/

@[expose] public section

open IsLocalRing AdicCompletion CategoryTheory AlgebraicGeometry

universe u v w

namespace MMP.Resolution.Bridges

section Auxiliary

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  (Ah : Type u) [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
  [IsHenselization A (ResidueField A) Ah]

private theorem isLocalHom_henselizationToAdicCompletion_algHom :
    IsLocalHom (henselizationToAdicCompletion A Ah) :=
  letI := isLocalHom_henselizationToAdicCompletion A Ah
  ⟨fun a ha => IsLocalHom.map_nonunit
    (f := (henselizationToAdicCompletion A Ah).toRingHom) a ha⟩

/-- An `A`-algebra map from an étale `A`-algebra into `Â` factors through the henselization. -/
theorem exists_algHom_henselization_of_etale
    (R' : Type u) [CommRing R'] [Algebra A R'] [Algebra.Etale A R']
    (τ : R' →ₐ[A] AdicCompletion (maximalIdeal A) A) :
    ∃ φ : R' →ₐ[A] Ah, ∀ y : R', henselizationToAdicCompletion A Ah (φ y) = τ y := by
  have : HenselianLocalRing Ah :=
    IsHenselization.henselian (R := A) (L := ResidueField A) (Rh := Ah)
  have : HenselianLocalRing (AdicCompletion (maximalIdeal A) A) :=
    henselianLocalRing_adicCompletion A (maximalIdeal A).fg_of_isNoetherianRing
  have : IsLocalHom (algebraMap A Ah) := IsHenselization.isLocalHom (L := ResidueField A)
  have := isLocalHom_henselizationToAdicCompletion_algHom A Ah
  set emb := henselizationToAdicCompletion A Ah with hemb
  set eT : ResidueField A ≃+* ResidueField (AdicCompletion (maximalIdeal A) A) :=
    RingEquiv.ofBijective _ (AdicCompletion.residueField_map_bijective A) with heT
  have hpt : ∀ y : ResidueField A,
      ResidueField.mapAlgHom emb (ResidueField.map (algebraMap A Ah) y) = eT y := by
    intro y
    obtain ⟨r, rfl⟩ := residue_surjective y
    change ResidueField.mapAlgHom emb (ResidueField.map (algebraMap A Ah) (residue A r)) =
      ResidueField.map (algebraMap A (AdicCompletion (maximalIdeal A) A)) (residue A r)
    rw [ResidueField.map_residue, ResidueField.map_residue,
      ResidueField.mapAlgHom_residue, emb.commutes r]
  set ψT : R' →ₐ[A] ResidueField (AdicCompletion (maximalIdeal A) A) :=
    { toRingHom := (residue (AdicCompletion (maximalIdeal A) A)).comp
        (τ : R' →+* AdicCompletion (maximalIdeal A) A)
      commutes' := fun r => by
        change residue (AdicCompletion (maximalIdeal A) A) (τ (algebraMap A R' r)) = _
        rw [τ.commutes r]
        rfl } with hψT
  have hψTapp : ∀ y : R', ψT y = residue (AdicCompletion (maximalIdeal A) A) (τ y) :=
    fun _ => rfl
  set ψh : R' →ₐ[A] ResidueField Ah :=
    { toRingHom := (ResidueField.map (algebraMap A Ah)).comp
        ((eT.symm : ResidueField (AdicCompletion (maximalIdeal A) A) →+* ResidueField A).comp
          (ψT : R' →+* ResidueField (AdicCompletion (maximalIdeal A) A)))
      commutes' := fun r => by
        change ResidueField.map (algebraMap A Ah) (eT.symm (ψT (algebraMap A R' r))) = _
        have h1 : ψT (algebraMap A R' r) = eT (residue A r) := by
          rw [hψTapp, τ.commutes r]
          change _ = ResidueField.map (algebraMap A (AdicCompletion (maximalIdeal A) A))
            (residue A r)
          rw [ResidueField.map_residue]
        rw [h1, eT.symm_apply_apply, ResidueField.map_residue]
        rfl } with hψh
  have hψhapp : ∀ y : R', ψh y =
      ResidueField.map (algebraMap A Ah) (eT.symm (ψT y)) := fun _ => rfl
  obtain ⟨φ, hφ, -⟩ := HenselianLocalRing.existsUnique_algHom_residue_of_etale
    (R := A) (A := R') (S := Ah) ψh
  obtain ⟨σ, -, huniq⟩ := HenselianLocalRing.existsUnique_algHom_residue_of_etale
    (R := A) (A := R') (S := AdicCompletion (maximalIdeal A) A) ψT
  have hcomp : emb.comp φ = τ := by
    refine (huniq _ fun y => ?_).trans (huniq τ fun y => (hψTapp y).symm).symm
    change residue (AdicCompletion (maximalIdeal A) A) (emb (φ y)) = ψT y
    rw [← ResidueField.mapAlgHom_residue emb (φ y), hφ y, hψhapp y, hpt (eT.symm (ψT y)),
      eT.apply_symm_apply]
  exact ⟨φ, fun y => AlgHom.congr_fun hcomp y⟩

end Auxiliary

variable {k : Type w} [Field k] {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [Algebra k A] [Algebra.EssFiniteType k A] (Ah : Type u) [CommRing Ah] [IsLocalRing Ah]
  [Algebra A Ah]
  [IsHenselization A (ResidueField A) Ah]
  {R : Type v} [CommRing R] [Algebra A R] [Algebra.FinitePresentation A R]

include k in
/-- **Approximation of a finitely presented map in the ordinary henselization.** Let `A` be a
local ring essentially of finite type over a field `k`, with henselization `Aʰ` and completion
`Â`. (That `A` is Noetherian, needed to form `Â` as a local ring, is automatic from essential
finite type, `Algebra.EssFiniteType.isNoetherianRing`; it is a redundant instance argument.)
For a finitely presented `A`-algebra `R` and an `A`-algebra map `φ : R → Â`, and every `N`,
there is an `A`-algebra map `ψ : R → Aʰ` whose composite with `Aʰ → Â` agrees with `φ` modulo
`𝔪ᴺ Â`. -/
@[mmp "thm_mmp_artin_approximation"]
theorem exists_algHom_henselization_approx
    (φ : R →ₐ[A] AdicCompletion (maximalIdeal A) A) (N : ℕ) :
    ∃ ψ : R →ₐ[A] Ah, ∀ x : R,
      φ x - henselizationToAdicCompletion A Ah (ψ x) ∈
        (maximalIdeal A ^ N).map (algebraMap A (AdicCompletion (maximalIdeal A) A)) := by
  classical
  have hG : IsGRing A :=
    isGRing_of_essFiniteType (R := k) (isGRing_basic_examples.{w, w}.1 k)
  obtain ⟨n, f, hf, hker⟩ := Algebra.FinitePresentation.out (R := A) (A := R)
  obtain ⟨m, g, hgspan⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hker
  have hgker : ∀ j, f (g j) = 0 := fun j =>
    (RingHom.mem_ker (f := f.toRingHom)).1 (hgspan ▸ Submodule.subset_span ⟨j, rfl⟩)
  set a : Fin n → AdicCompletion (maximalIdeal A) A := fun i => φ (f (MvPolynomial.X i))
  have hφa : (φ.comp f) = MvPolynomial.aeval a := by
    ext i
    simp [a]
  have hsol : ∀ j, MvPolynomial.aeval a (g j) = 0 := fun j => by
    rw [← hφa]
    simp [hgker]
  obtain ⟨σ, -, τ, -, -, hτ⟩ :=
    Stacks.Smoothing.exists_localEtaleSolution_of_isGRing hG g N a hsol
  obtain ⟨χ, hχ⟩ := exists_algHom_henselization_of_etale A Ah σ.carrier τ
  set b : Fin n → Ah := fun i => χ (σ.sol i)
  have hbsol : ∀ j, MvPolynomial.aeval b (g j) = 0 := fun j => by
    have h1 := σ.eval_sol j
    rw [← MvPolynomial.aeval_def] at h1
    have : MvPolynomial.aeval b (g j) = χ (MvPolynomial.aeval σ.sol (g j)) := by
      rw [← AlgHom.comp_apply]
      congr 1
      ext i
      simp [b]
    rw [this, h1, _root_.map_zero]
  have hkerle : RingHom.ker f.toRingHom ≤
      RingHom.ker (MvPolynomial.aeval b : _ →ₐ[A] Ah).toRingHom := by
    rw [← hgspan, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hbsol j
  set I := (maximalIdeal A ^ N).map (algebraMap A (AdicCompletion (maximalIdeal A) A))
  let q : AdicCompletion (maximalIdeal A) A →ₐ[A] (AdicCompletion (maximalIdeal A) A ⧸ I) :=
    Ideal.Quotient.mkₐ A I
  let emb := henselizationToAdicCompletion A Ah
  have hq : q.comp (MvPolynomial.aeval a) = q.comp (emb.comp (MvPolynomial.aeval b)) := by
    ext i
    have h1 : emb (b i) = τ (σ.sol i) := hχ _
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, q, Ideal.Quotient.mkₐ_eq_mk, h1, b]
    rw [Ideal.Quotient.eq]
    exact hτ i
  refine ⟨f.liftOfSurjective hf _ hkerle, fun x => ?_⟩
  obtain ⟨p, rfl⟩ := hf x
  rw [AlgHom.liftOfSurjective_apply, ← Ideal.Quotient.eq]
  have := AlgHom.congr_fun hq p
  simp only [AlgHom.comp_apply, q, Ideal.Quotient.mkₐ_eq_mk] at this
  have h2 : φ (f p) = MvPolynomial.aeval a p := AlgHom.congr_fun hφa p
  rw [h2, this]

end MMP.Resolution.Bridges
