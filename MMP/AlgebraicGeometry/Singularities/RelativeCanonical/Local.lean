module

public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.HigherTrace.ReflexiveHullExtension
public import StacksFrontier.AlgebraicGeometry.DeRham.FormsGeneratorCalculus
public import StacksFrontier.AlgebraicGeometry.NormInvertible.PullbackGenerator

@[expose] public noncomputable section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry
open Stacks.RelativeDifferentialStalkMap

namespace MMP.Intersection

/-! ### Top exterior powers -/

/-- An order embedding of `Fin n` into itself is the identity. -/
theorem _root_.MMP.FinAux.coe_orderEmbedding_eq_id {n : ℕ} (e : Fin n ↪o Fin n) : ⇑e = id := by
  have hs : Function.Bijective e := Finite.injective_iff_bijective.mp e.injective
  have h := Subsingleton.elim (StrictMono.orderIsoOfSurjective e e.strictMono hs.2)
    (OrderIso.refl (Fin n))
  funext i
  exact congrArg (fun g : Fin n ≃o Fin n => g i) h

/-- **The top exterior power of a free module of rank `n`** is free of rank one on the wedge
`b₁ ∧ ⋯ ∧ bₙ` of any basis: `r ↦ r • (b₁ ∧ ⋯ ∧ bₙ)` is bijective. -/
theorem bijective_smul_ιMulti_basis {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    {n : ℕ} (b : Module.Basis (Fin n) A M) :
    Function.Bijective fun r : A => r • exteriorPower.ιMulti A n b := by
  classical
  let B := b.exteriorPower n
  have he : ∀ s : Set.powersetCard (Fin n) n,
      B s = exteriorPower.ιMulti A n b := by
    intro s
    rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family,
      FinAux.coe_orderEmbedding_eq_id (Set.powersetCard.ofFinEmbEquiv.symm s), Function.comp_id]
  let s₀ : Set.powersetCard (Fin n) n :=
    Set.powersetCard.ofFinEmbEquiv (OrderIso.refl (Fin n)).toOrderEmbedding
  have hsub : ∀ s : Set.powersetCard (Fin n) n, s = s₀ := by
    intro s
    apply Set.powersetCard.ofFinEmbEquiv.symm.injective
    apply DFunLike.coe_injective
    rw [FinAux.coe_orderEmbedding_eq_id, FinAux.coe_orderEmbedding_eq_id]
  refine ⟨fun r r' h => ?_, fun m => ⟨B.repr m s₀, ?_⟩⟩
  · have h' : r • B s₀ = r' • B s₀ := by simpa only [he] using h
    simpa using congrArg (fun m => B.repr m s₀) h'
  · have hm := B.sum_repr m
    rw [Fintype.sum_eq_single s₀ (fun s hs => absurd (hsub s) hs)] at hm
    simpa only [he] using hm

/-! ### Differentials of a regular system of parameters -/

section RegularParameters

open IsLocalRing KaehlerDifferential TensorProduct

variable {R A : Type*} [CommRing R] [CommRing A] [IsLocalRing A] [Algebra R A]

/-- The classes in the cotangent space `𝔪/𝔪²` of a regular system of parameters are linearly
independent over the residue field. -/
theorem linearIndependent_toCotangent_of_isRegularSystemOfParameters [IsNoetherianRing A] {n : ℕ}
    {z : Fin n → A} (hz : MMP.Mori.IsRegularSystemOfParameters z)
    (hzm : ∀ j, z j ∈ maximalIdeal A) :
    LinearIndependent (ResidueField A) fun j => (maximalIdeal A).toCotangent ⟨z j, hzm j⟩ := by
  let κ := ResidueField A
  let c : Fin n → CotangentSpace A := fun j => (maximalIdeal A).toCotangent ⟨z j, hzm j⟩
  have hspan : ⊤ ≤ Submodule.span κ (Set.range c) := by
    intro w _
    obtain ⟨⟨w, hw⟩, rfl⟩ := (maximalIdeal A).toCotangent_surjective w
    rw [← hz.1] at hw
    refine Submodule.span_induction (p := fun y hy =>
      (maximalIdeal A).toCotangent ⟨y, hz.1 ▸ hy⟩ ∈ Submodule.span κ (Set.range c)) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨j, rfl⟩
      exact Submodule.subset_span ⟨j, rfl⟩
    · rw [show (⟨0, _⟩ : maximalIdeal A) = 0 from rfl, map_zero]
      exact Submodule.zero_mem _
    · intro y y' hy hy' hy₁ hy₂
      have := Submodule.add_mem _ hy₁ hy₂
      rwa [← map_add] at this
    · intro r y hy hy₁
      have := Submodule.smul_mem _ (algebraMap A κ r) hy₁
      rwa [algebraMap_smul, ← map_smul] at this
  have hcard : Fintype.card (Fin n) = Module.finrank κ (CotangentSpace A) := by
    have h := (IsRegularLocalRing.iff_finrank_cotangentSpace A).mp
      (MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz)
    rw [hz.2] at h
    simpa using (Nat.cast_inj.mp (WithBot.coe_inj.mp (by exact_mod_cast h))).symm
  exact linearIndependent_of_top_le_span_of_card_eq_finrank hspan hcard

/-- The residue classes in `κ ⊗_A Ω_{A/R}` of the differentials of a regular system of parameters
are linearly independent over the residue field, for `κ` formally smooth over `R`: no
combination `∑ aᵢ dzᵢ` with a coefficient outside `𝔪` vanishes modulo `𝔪`. -/
theorem mem_maximalIdeal_of_sum_smul_tmul_D_eq_zero [IsNoetherianRing A]
    [Algebra.FormallySmooth R A] [Algebra.FormallySmooth R (ResidueField A)] {n : ℕ}
    {z : Fin n → A} (hz : MMP.Mori.IsRegularSystemOfParameters z) (a : Fin n → A)
    (ha : ∑ i, a i • ((1 : ResidueField A) ⊗ₜ[A] D R A (z i)) = 0) (i : Fin n) :
    a i ∈ maximalIdeal A := by
  classical
  let κ := ResidueField A
  have hzm : ∀ j, z j ∈ maximalIdeal A := fun j => hz.1 ▸ Ideal.subset_span ⟨j, rfl⟩
  have hker : RingHom.ker (algebraMap A κ) = maximalIdeal A := IsLocalRing.ker_residue
  set x : A := ∑ j, a j * z j with hxdef
  have hxm : x ∈ maximalIdeal A := Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hzm j)
  have hxI : x ∈ RingHom.ker (algebraMap A κ) := hker ▸ hxm
  have hD : (1 : κ) ⊗ₜ[A] D R A x = ∑ j, a j • ((1 : κ) ⊗ₜ[A] D R A (z j)) := by
    rw [hxdef, map_sum, tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : algebraMap A κ (z j) = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr (hzm j)
    rw [Derivation.leibniz, tmul_add, tmul_smul, tmul_smul, add_eq_left, smul_tmul',
      Algebra.smul_def, mul_one, this, zero_tmul]
  have hinj : Function.Injective (kerCotangentToTensor R A κ) :=
    (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff
      IsLocalRing.residue_surjective).mpr ((Algebra.formallySmooth_iff R κ).mp inferInstance).2
  have hx0 : (RingHom.ker (algebraMap A κ)).toCotangent ⟨x, hxI⟩ = 0 := by
    apply hinj
    rw [kerCotangentToTensor_toCotangent, map_zero]
    exact hD.trans ha
  have hx2 : x ∈ maximalIdeal A ^ 2 := hker ▸ (Ideal.toCotangent_eq_zero _ _).mp hx0
  let c : Fin n → CotangentSpace A := fun j => (maximalIdeal A).toCotangent ⟨z j, hzm j⟩
  have hli := linearIndependent_toCotangent_of_isRegularSystemOfParameters hz hzm
  have hsum : ∑ j, algebraMap A κ (a j) • c j = 0 := by
    rw [← ((maximalIdeal A).toCotangent_eq_zero ⟨x, hxm⟩).mpr hx2]
    simp only [algebraMap_smul, c, ← map_smul]
    rw [← map_sum]
    congr 1
    ext
    simp [hxdef, smul_eq_mul]
  exact (IsLocalRing.residue_eq_zero_iff _).mp (Fintype.linearIndependent_iff.mp hli _ hsum i)

/-- **The differentials of a regular system of parameters form a basis.** Let `A` be a
Noetherian local ring, formally smooth and essentially of finite type over `R`, with residue field
formally smooth over `R`, and with `Ω_{A/R}` of rank `n`. Then for a regular system of parameters
`z₁, …, zₙ` of `A`, the differentials `dz₁, …, dzₙ` are a basis of `Ω_{A/R}`. -/
theorem exists_basis_D_of_isRegularSystemOfParameters [IsNoetherianRing A]
    [Algebra.FormallySmooth R A] [Algebra.EssFiniteType R A]
    [Algebra.FormallySmooth R (ResidueField A)] {n : ℕ} (hn : Module.finrank A Ω[A⁄R] = n)
    {z : Fin n → A} (hz : MMP.Mori.IsRegularSystemOfParameters z) :
    ∃ b : Module.Basis (Fin n) A Ω[A⁄R], ⇑b = fun i => D R A (z i) := by
  classical
  let κ := ResidueField A
  have : Module.Finite A Ω[A⁄R] := KaehlerDifferential.finite R A
  have : Module.Projective A Ω[A⁄R] := ((Algebra.formallySmooth_iff R A).mp inferInstance).1
  have : Module.Free A Ω[A⁄R] := Module.free_of_flat_of_isLocalRing
  let v : Fin n → κ ⊗[A] Ω[A⁄R] := fun i => (1 : κ) ⊗ₜ[A] D R A (z i)
  have hv : LinearIndependent κ v := by
    refine Fintype.linearIndependent_iff.mpr fun g hg i => ?_
    choose a ha using fun j => IsLocalRing.residue_surjective (g j)
    have hsum : ∑ j, a j • v j = 0 := by
      rw [← hg]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← ha j]
      exact (algebraMap_smul κ (a j) (v j)).symm
    rw [← ha i]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr
      (mem_maximalIdeal_of_sum_smul_tmul_D_eq_zero hz a hsum i)
  have hcard : Fintype.card (Fin n) = Module.finrank κ (κ ⊗[A] Ω[A⁄R]) := by
    rw [Module.finrank_baseChange, hn, Fintype.card_fin]
  have hspan : Submodule.span A (Set.range fun i => D R A (z i)) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis _
      (Module.Basis.mk hv (Submodule.eq_top_of_finrank_eq
        ((finrank_span_eq_card hv).trans hcard)).ge) fun i => by
      simp only [v, Module.Basis.coe_mk]
  have hli : LinearIndependent A fun i => D R A (z i) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge (by rw [hn, Fintype.card_fin])
  exact ⟨Module.Basis.mk hli hspan.ge, Module.Basis.coe_mk _ _⟩

/-- For a regular system of parameters `z₁, …, zₙ` as in
`MMP.Intersection.exists_basis_D_of_isRegularSystemOfParameters`, the module `⋀ⁿ Ω_{A/R}` is
free of rank one on `dz₁ ∧ ⋯ ∧ dzₙ`. -/
theorem bijective_smul_ιMulti_D_of_isRegularSystemOfParameters [IsNoetherianRing A]
    [Algebra.FormallySmooth R A] [Algebra.EssFiniteType R A]
    [Algebra.FormallySmooth R (ResidueField A)] {n : ℕ} (hn : Module.finrank A Ω[A⁄R] = n)
    {z : Fin n → A} (hz : MMP.Mori.IsRegularSystemOfParameters z) :
    Function.Bijective fun r : A => r • exteriorPower.ιMulti A n fun i => D R A (z i) := by
  obtain ⟨b, hb⟩ := exists_basis_D_of_isRegularSystemOfParameters hn hz
  rw [← hb]
  exact bijective_smul_ιMulti_basis b

end RegularParameters

variable {X S : Scheme.{u}}

/-- The isomorphism `⋀ⁿ M ≃ ⋀ⁿ N` induced by a linear equivalence `e : M ≃ N` sends
`m₁ ∧ ⋯ ∧ mₙ` to `e m₁ ∧ ⋯ ∧ e mₙ`. -/
theorem extCongr_ιMulti {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (n : ℕ) (e : M ≃ₗ[R] N) (m : Fin n → M) :
    extCongr n e (exteriorPower.ιMulti R n m) = exteriorPower.ιMulti R n (fun i => e (m i)) :=
  exteriorPower.map_apply_ιMulti _ _

/-- Under the identification of the stalk at `x` of the sheaf of relative `n`-forms of `f` with
`⋀ⁿ Ω_{𝒪_{X,x}/𝒪_{S,f x}}`, the germ of the section `dg₁ ∧ ⋯ ∧ dgₙ` over `U` is the wedge of the
Kähler differentials of the germs of the `gᵢ`. -/
theorem formsStalkEquiv_germ_gen (f : X ⟶ S) {U : X.Opens} {x : X} (hx : x ∈ U) {n : ℕ}
    (g : Fin n → Γ(X, U)) :
    letI := algebraStalkMap f x
    formsStalkEquiv f n x
        (TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials f).exteriorAlgebra.piece
          (n : ℤ)).val.presheaf U x hx (Stacks.DeRham.FormsGenerators.gen f U g)) =
      exteriorPower.ιMulti _ n fun i =>
        KaehlerDifferential.D (ToType (S.presheaf.stalk (f x))) (ToType (X.sheaf.presheaf.stalk x))
          (X.presheaf.germ U x hx (g i)) := by
  let := algebraStalkMap f x
  let := Classical.decEq (OrderDual (TopologicalSpace.OpenNhds x))
  rw [formsStalkEquiv, LinearEquiv.trans_apply, Stacks.DeRham.FormsGenerators.gen,
    Stacks.GradedAlgebra.homogeneousProdLeft_eq_homogeneousProd]
  have h := SheafOfModules.exteriorPowerStalkEquiv_germ_homogeneousProd
    (Scheme.Modules.exteriorAlgebra (Scheme.Hom.relativeDifferentials f))
    (Scheme.Modules.exteriorGenerator _)
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _) n x U hx
    (fun i => (Scheme.Hom.universalRelativeDerivation f).d (g i))
  refine ((congrArg (extCongr n (relativeDifferentialsStalkKaehlerEquiv f x)) h).trans
    (extCongr_ιMulti _ _ _)).trans ?_
  congr 1
  funext i
  exact relativeDifferentialsStalkKaehlerEquiv_germ_d f x (OrderDual.toDual ⟨U, hx⟩) (g i)

end MMP.Intersection
