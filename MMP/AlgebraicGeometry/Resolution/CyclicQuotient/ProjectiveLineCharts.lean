module
public import MMP.AlgebraicGeometry.Resolution.CyclicQuotient.NodeRing
public import StacksFrontier.AlgebraicGeometry.NormInvertible.PullbackGenerator
public import StacksFrontier.AlgebraicGeometry.PicardUFD.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.CoefficientAlgebra
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineProjModel
public import StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.TensorTotalComplex

/-!
# Charts of the projective line and chart generators

We glue morphisms out of the projective line from its two standard charts, recognise a scheme
over a field `K` covered by two affine lines `Spec K[X]` with coordinates inverse on the overlap
as the projective line, and describe invertible sheaves on such curves and their thickenings by
generators on the charts.

## Main definitions

* `chartMap`: the open immersion `Spec K[X] ⟶ C` of an affine open with coordinate ring `K[X]`.
* `sigmaSub`: the structure constants `K → Γ(Z, Z ∩ U)` of a closed subscheme `Z`.
* `awayCoord`: the identification of the sections of `Proj` over `D₊(f)` with `(A_f)₀`.

## Main results

* `free_of_invertible_chart`: invertible modules over `K[x, y]/(y)`, `K[x, y]/(x)` and
  `K[x, y]/(x y)` are free.
* `exists_hom_projectiveLine`: morphisms out of the projective line glue from the two charts.
* `exists_iso_projectiveLine`: a `K`-scheme covered by two compatible affine lines is
  isomorphic to the projective line.
* `exists_epsilon_data'`: a closed subscheme with suitable chart generators is isomorphic over
  `K` to the projective line.
* `iso_twist_of_generators`: an invertible sheaf on `Proj R[T₀, T₁]` with transition
  `a · (T₁/T₀)^m` is isomorphic to `𝒪(m)`.
* `final_iso_core2`: the pullback of an invertible sheaf to the projective line along a chart
  identification is `𝒪(-n)`, `n` read off from its transition unit.
* `exists_coeff_generator`: the canonical section of an effective Cartier divisor is a
  coefficient times a generator on an affine chart of a thickening.
-/

open AlgebraicGeometry hiding PrimeDivisor
open CategoryTheory Opposite MMP.Mori

namespace MMP.Resolution.MarkedChain

universe u

@[expose] public section

section D2Lemmas

open TopologicalSpace Polynomial LaurentPolynomial

/-- `K[x,y]/(y) ≅ K[X]`: a surjection from `K[x,y]` with kernel `(y)` is a polynomial ring in the
image of `x`. -/
theorem exists_algEquiv_polynomial {K : Type u} [Field K] {B : Type u} [CommRing B] [Algebra K B]
    (φ : MvPolynomial (Fin 2) K →ₐ[K] B) (hs : Function.Surjective φ)
    (hk : RingHom.ker φ = Ideal.span {MvPolynomial.X 1}) :
    ∃ e : K[X] ≃ₐ[K] B, e X = φ (MvPolynomial.X 0) := by
  let ε0 : MvPolynomial (Fin 2) K →ₐ[K] K[X] := MvPolynomial.aeval ![X, 0]
  let ι : K[X] →ₐ[K] MvPolynomial (Fin 2) K := Polynomial.aeval (MvPolynomial.X 0)
  let ψ : K[X] →ₐ[K] B := φ.comp ι
  have hψX : ψ X = φ (MvPolynomial.X 0) := by simp [ψ, ι]
  have hεy : ε0 (MvPolynomial.X 1) = 0 := by simp [ε0]
  have hει : ε0.comp ι = AlgHom.id K K[X] := by
    refine Polynomial.algHom_ext ?_
    simp [ε0, ι]
  have hy : φ (MvPolynomial.X 1) = 0 := by
    rw [← RingHom.mem_ker, hk]
    exact Ideal.subset_span rfl
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    have hmem : ι f ∈ RingHom.ker φ := hf
    rw [hk] at hmem
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
    have := congrArg ε0 hc
    rw [map_mul, hεy, mul_zero] at this
    have h2 := congrArg (fun a => a f) hει
    simp only [AlgHom.comp_apply, AlgHom.id_apply] at h2
    rw [h2] at this
    exact this.symm
  have hsurj : Function.Surjective ψ := by
    intro b
    obtain ⟨z, rfl⟩ := hs b
    refine ⟨ε0 z, ?_⟩
    have hφ : φ = ψ.comp ε0 := by
      refine MvPolynomial.algHom_ext fun i => ?_
      fin_cases i
      · simp [ψ, ι, ε0]
      · simp [hy, ε0]
    exact (congrArg (fun χ => χ z) hφ).symm
  exact ⟨AlgEquiv.ofBijective ψ ⟨hinj, hsurj⟩, hψX⟩

/-- `K[x,y]/(x) ≅ K[X]`: a surjection from `K[x,y]` with kernel `(x)` is a polynomial ring in the
image of `y`. -/
theorem exists_algEquiv_polynomial' {K : Type u} [Field K] {B : Type u} [CommRing B] [Algebra K B]
    (φ : MvPolynomial (Fin 2) K →ₐ[K] B) (hs : Function.Surjective φ)
    (hk : RingHom.ker φ = Ideal.span {MvPolynomial.X 0}) :
    ∃ e : K[X] ≃ₐ[K] B, e X = φ (MvPolynomial.X 1) := by
  let σ : MvPolynomial (Fin 2) K ≃ₐ[K] MvPolynomial (Fin 2) K :=
    MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin 2) 1)
  have hσ0 : σ (MvPolynomial.X 0) = MvPolynomial.X 1 := by simp [σ]
  have hσ1 : σ (MvPolynomial.X 1) = MvPolynomial.X 0 := by simp [σ]
  have hσσ : ∀ w, σ (σ w) = w := fun w => by
    simp only [σ, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_rename]
    have h : ⇑(Equiv.swap (0 : Fin 2) 1) ∘ ⇑(Equiv.swap (0 : Fin 2) 1) = id := by
      ext i; simp
    rw [h, MvPolynomial.rename_id]
    rfl
  obtain ⟨e, he⟩ := exists_algEquiv_polynomial (φ.comp σ.toAlgHom)
    (hs.comp σ.surjective) (by
      ext z
      rw [RingHom.mem_ker, Ideal.mem_span_singleton]
      have hz : φ (σ z) = 0 ↔ MvPolynomial.X 0 ∣ σ z := by
        rw [← Ideal.mem_span_singleton, ← hk]; rfl
      change φ (σ z) = 0 ↔ _
      rw [hz]
      constructor
      · rintro ⟨c, hc⟩
        exact ⟨σ c, by simpa only [hσσ, map_mul, hσ0] using congrArg σ hc⟩
      · rintro ⟨c, hc⟩
        exact ⟨σ c, by simpa only [map_mul, hσ1] using congrArg σ hc⟩)
  exact ⟨e, by rw [he]; simp [hσ0]⟩

/-- If `A` is a quotient of `K[x, y]` with kernel `(x y)`, the quotient of `A` by the image of
either variable is a principal ideal domain. -/
theorem prin_quot_chart {K : Type u} [Field K] {A : Type u} [CommRing A]
    (φ : MvPolynomial (Fin 2) K →+* A) (hs : Function.Surjective φ)
    (hk : RingHom.ker φ = Ideal.span {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) K)})
    (w : Fin 2) :
    IsDomain (A ⧸ Ideal.span {φ (MvPolynomial.X w)}) ∧
      IsPrincipalIdealRing (A ⧸ Ideal.span {φ (MvPolynomial.X w)}) := by
  let I : Ideal A := Ideal.span {φ (MvPolynomial.X w)}
  let ψ : MvPolynomial (Fin 2) K →+* A ⧸ I := (Ideal.Quotient.mk I).comp φ
  have hψs : Function.Surjective ψ := (Ideal.Quotient.mk_surjective).comp hs
  letI : Algebra K (A ⧸ I) := (ψ.comp MvPolynomial.C).toAlgebra
  let ψa : MvPolynomial (Fin 2) K →ₐ[K] A ⧸ I :=
    { ψ with commutes' := fun c => rfl }
  have hker : RingHom.ker ψ = Ideal.span {(MvPolynomial.X w : MvPolynomial (Fin 2) K)} := by
    ext p
    rw [RingHom.mem_ker, Ideal.mem_span_singleton]
    change Ideal.Quotient.mk I (φ p) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨r, hr⟩
      obtain ⟨q, rfl⟩ := hs r
      have : p - q * MvPolynomial.X w ∈ RingHom.ker φ := by
        rw [RingHom.mem_ker, map_sub, map_mul, hr, sub_self]
      rw [hk, Ideal.mem_span_singleton] at this
      obtain ⟨c, hc⟩ := this
      refine ⟨q + c * (if w = 0 then MvPolynomial.X 1 else MvPolynomial.X 0), ?_⟩
      fin_cases w <;> (simp at hc ⊢; linear_combination hc)
    · rintro ⟨q, rfl⟩
      exact ⟨φ q, by rw [map_mul, mul_comm]⟩
  have hdp : ∀ e : Polynomial K ≃ₐ[K] A ⧸ I, IsDomain (A ⧸ I) ∧ IsPrincipalIdealRing (A ⧸ I) :=
    fun e => ⟨Function.Injective.isDomain e.symm.toRingEquiv.toRingHom e.symm.injective,
      IsPrincipalIdealRing.of_surjective e.toRingEquiv.toRingHom e.surjective⟩
  fin_cases w
  · obtain ⟨e, -⟩ := exists_algEquiv_polynomial' ψa hψs hker
    exact hdp e
  · obtain ⟨e, -⟩ := exists_algEquiv_polynomial ψa hψs hker
    exact hdp e

/-- A polynomial in two variables with zero constant coefficient lies in the ideal `(X 0, X 1)`. -/
theorem mem_span_X_of_constantCoeff {K : Type u} [Field K] (p : MvPolynomial (Fin 2) K)
    (h : MvPolynomial.constantCoeff p = 0) :
    p ∈ Ideal.span ({MvPolynomial.X 0, MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) K)) := by
  have : ({MvPolynomial.X 0, MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) K)) =
      MvPolynomial.X '' (Set.univ : Set (Fin 2)) := by
    ext z; simp [Fin.exists_fin_two, eq_comm]
  rw [this, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [MvPolynomial.mem_support_iff, ← MvPolynomial.constantCoeff_eq] at hm
    exact hm h
  by_contra hcon
  push Not at hcon
  apply hm0
  ext i
  simpa using hcon i (Set.mem_univ i)

/-- If `A` is a quotient of `K[x, y]` with kernel `(x y)`, every invertible `A`-module is free. -/
theorem free_of_invertible_node_chart {K : Type u} [Field K] {A : Type u} [CommRing A]
    (φ : MvPolynomial (Fin 2) K →+* A) (hs : Function.Surjective φ)
    (hk : RingHom.ker φ = Ideal.span {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) K)})
    (M' : Type u) [AddCommGroup M'] [Module A M'] [Module.Invertible A M'] : Module.Free A M' := by
  obtain ⟨d0, p0⟩ := prin_quot_chart φ hs hk 0
  obtain ⟨d1, p1⟩ := prin_quot_chart φ hs hk 1
  let I : Ideal A := Ideal.span {φ (MvPolynomial.X 0)}
  let J : Ideal A := Ideal.span {φ (MvPolynomial.X 1)}
  have hIJ : I * J = ⊥ := by
    rw [Ideal.span_singleton_mul_span_singleton, ← map_mul, Ideal.span_singleton_eq_bot,
      ← RingHom.mem_ker, hk]
    exact Ideal.subset_span rfl
  have hsup : ∀ p : MvPolynomial (Fin 2) K, MvPolynomial.constantCoeff p = 0 → φ p ∈ I ⊔ J := by
    intro p hp
    have h := Ideal.mem_map_of_mem φ (mem_span_X_of_constantCoeff p hp)
    rw [Ideal.map_span] at h
    refine Ideal.span_le.2 ?_ h
    rintro _ ⟨z, hz, rfl⟩
    rcases hz with rfl | rfl
    · exact Ideal.mem_sup_left (Ideal.subset_span rfl)
    · exact Ideal.mem_sup_right (Ideal.subset_span rfl)
  let e := RingHom.quotientKerEquivOfSurjective hs
  have hker0 : RingHom.ker φ ≤ RingHom.ker (MvPolynomial.constantCoeff (R := K) (σ := Fin 2)) := by
    rw [hk, Ideal.span_le, Set.singleton_subset_iff]
    simp
  let ε : A →+* K := (Ideal.Quotient.lift (RingHom.ker φ) MvPolynomial.constantCoeff
    (fun a ha => hker0 ha)).comp e.symm.toRingHom
  have hε : ∀ p, ε (φ p) = MvPolynomial.constantCoeff p := by
    intro p
    have : e.symm (φ p) = Ideal.Quotient.mk (RingHom.ker φ) p := by
      rw [RingEquiv.symm_apply_eq]; rfl
    show (Ideal.Quotient.lift (RingHom.ker φ) (MvPolynomial.constantCoeff (R := K) (σ := Fin 2))
      (fun a ha => hker0 ha)) (e.symm (φ p)) = _
    rw [this]; exact Ideal.Quotient.lift_mk _ _ _
  have hle : I ⊔ J ≤ RingHom.ker ε := by
    refine sup_le ?_ ?_ <;>
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, hε] <;> simp
  have hne : I ⊔ J ≠ ⊤ := fun h => by
    have := hle ((Ideal.eq_top_iff_one _).1 h)
    rw [RingHom.mem_ker, map_one] at this
    exact one_ne_zero this
  have hU : ∀ r : A, r ∉ I ⊔ J → ∃ s : Aˣ, (s : A) - r ∈ I ⊔ J := by
    intro r hr
    obtain ⟨p, rfl⟩ := hs r
    have hc : MvPolynomial.constantCoeff p ≠ 0 := fun h => hr (hsup p h)
    have hu : IsUnit (φ (MvPolynomial.C (MvPolynomial.constantCoeff p))) :=
      (isUnit_iff_ne_zero.2 hc).map (φ.comp MvPolynomial.C)
    refine ⟨hu.unit, ?_⟩
    rw [IsUnit.unit_spec, ← map_sub]
    exact hsup _ (by simp)
  exact free_of_glue I J hIJ hne hU

/-- If `A` is a quotient of `K[x, y]` whose kernel is generated by one variable, every invertible
`A`-module is free. -/
theorem free_of_invertible_axis {K : Type u} [Field K] {A : Type u} [CommRing A]
    (φ : MvPolynomial (Fin 2) K →+* A) (hs : Function.Surjective φ) (v : Fin 2)
    (hk : RingHom.ker φ = Ideal.span {(MvPolynomial.X v : MvPolynomial (Fin 2) K)})
    (M' : Type u) [AddCommGroup M'] [Module A M'] [Module.Invertible A M'] : Module.Free A M' := by
  letI : Algebra K A := (φ.comp MvPolynomial.C).toAlgebra
  let φa : MvPolynomial (Fin 2) K →ₐ[K] A := { φ with commutes' := fun c => rfl }
  have hdp : ∀ e : Polynomial K ≃ₐ[K] A, Module.Free A M' := by
    intro e
    haveI : IsDomain A := Function.Injective.isDomain e.symm.toRingEquiv.toRingHom e.symm.injective
    haveI : IsPrincipalIdealRing A := IsPrincipalIdealRing.of_surjective e.toRingEquiv.toRingHom e.surjective
    infer_instance
  fin_cases v
  · obtain ⟨e, -⟩ := exists_algEquiv_polynomial' φa hs hk
    exact hdp e
  · obtain ⟨e, -⟩ := exists_algEquiv_polynomial φa hs hk
    exact hdp e

/-- If `A` is a quotient of `K[x, y]` with kernel `(y)`, `(x)` or `(x y)`, every invertible
`A`-module is free. -/
theorem free_of_invertible_chart {K : Type u} [Field K] {A : Type u} [CommRing A]
    (φ : MvPolynomial (Fin 2) K →+* A) (hs : Function.Surjective φ)
    {J : Ideal (MvPolynomial (Fin 2) K)} (hk : RingHom.ker φ = J)
    (hJ : J = Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 2) K)} ∨
      J = Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) K)} ∨
      J = Ideal.span {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) K)})
    (M' : Type u) [AddCommGroup M'] [Module A M'] [Module.Invertible A M'] : Module.Free A M' := by
  rcases hJ with h | h | h
  · exact free_of_invertible_axis φ hs 1 (hk.trans h) M'
  · exact free_of_invertible_axis φ hs 0 (hk.trans h) M'
  · exact free_of_invertible_node_chart φ hs (hk.trans h) M'

/-- Let `p : K[x, y] → A₀` be surjective with kernel contained in `(q)`, and let `s₀ : Γ → A₀` be
surjective with `(s₀ g) = (p q)`. If the kernel of `r ∘ s₀` is `(g)`, then the kernel of `r ∘ p`
is `(q)`. -/
theorem ker_comp_eq_span {K : Type u} [Field K] {Γ A0 AC : Type u} [CommRing Γ] [CommRing A0]
    [CommRing AC] [Algebra K A0] [Algebra K AC]
    (s0 : Γ →+* A0) (hs0 : Function.Surjective s0) (r : A0 →ₐ[K] AC) (g : Γ)
    (hg : RingHom.ker ((r : A0 →+* AC).comp s0) = Ideal.span {g})
    (p : MvPolynomial (Fin 2) K →ₐ[K] A0) (hp : Function.Surjective p)
    (q : MvPolynomial (Fin 2) K) (hpq : RingHom.ker p ≤ Ideal.span {q})
    (hgq : Ideal.span {s0 g} = Ideal.span {p q}) :
    RingHom.ker (r.comp p) = Ideal.span {q} := by
  have hr : ∀ a, r a = 0 ↔ a ∈ Ideal.span {p q} := by
    intro a
    rw [← hgq]
    constructor
    · intro h
      obtain ⟨γ, rfl⟩ := hs0 a
      have : γ ∈ RingHom.ker ((r : A0 →+* AC).comp s0) := h
      rw [hg, Ideal.mem_span_singleton] at this
      obtain ⟨c, rfl⟩ := this
      rw [Ideal.mem_span_singleton]
      exact ⟨s0 c, by rw [map_mul]⟩
    · intro h
      rw [Ideal.mem_span_singleton] at h
      obtain ⟨c, rfl⟩ := h
      have h0 : g ∈ RingHom.ker ((r : A0 →+* AC).comp s0) := by
        rw [hg]; exact Ideal.subset_span rfl
      rw [map_mul, show r (s0 g) = 0 from h0, zero_mul]
  ext z
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  change r (p z) = 0 ↔ _
  rw [hr, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨c', rfl⟩ := hp c
    have hz : z - q * c' ∈ RingHom.ker p := by
      rw [RingHom.mem_ker, map_sub, map_mul, hc]; ring
    have := hpq hz
    rw [Ideal.mem_span_singleton] at this
    obtain ⟨d, hd⟩ := this
    exact ⟨d + c', by linear_combination hd⟩
  · rintro ⟨c, rfl⟩
    exact ⟨p c, by rw [map_mul]⟩

/-- Let `K[x, y] → A₀`, `x ↦ x₀`, `y ↦ y₀`, be surjective with kernel contained in `(y)`, and let
`r : A₀ → A_C` be compatible with surjections `s₀ : Γ → A₀` and `s_C : Γ → A_C` such that
`ker s_C = (g)` and `s₀ g = y₀`. Then `A_C` is a polynomial ring over `K` in `r x₀`. -/
theorem bridge_chart_alg {K : Type u} [Field K] {Γ A0 AC : Type u} [CommRing Γ] [CommRing A0]
    [CommRing AC] (σS : K →+* A0) (σC : K →+* AC) (s0 : Γ →+* A0)
    (hs0 : Function.Surjective s0) (sC : Γ →+* AC) (hsC : Function.Surjective sC)
    (r : A0 →+* AC) (hrs : ∀ γ, r (s0 γ) = sC γ) (hσ : ∀ k, r (σS k) = σC k) (g : Γ)
    (hker : RingHom.ker sC = Ideal.span {g}) (x0 y0 : A0)
    (hs : Function.Surjective (MvPolynomial.eval₂Hom σS ![x0, y0]))
    (hk : RingHom.ker (MvPolynomial.eval₂Hom σS ![x0, y0]) ≤ Ideal.span {MvPolynomial.X 1})
    (hgy : s0 g = y0) :
    ∃ e : K[X] ≃+* AC, (∀ k, e (Polynomial.C k) = σC k) ∧ e X = r x0 := by
  letI : Algebra K A0 := σS.toAlgebra
  letI : Algebra K AC := σC.toAlgebra
  let r' : A0 →ₐ[K] AC := { r with commutes' := hσ }
  let p : MvPolynomial (Fin 2) K →ₐ[K] A0 := MvPolynomial.aeval ![x0, y0]
  have hps : Function.Surjective p := hs
  have hrsurj : Function.Surjective r' := by
    intro c
    obtain ⟨γ, rfl⟩ := hsC c
    exact ⟨s0 γ, hrs γ⟩
  have hgker : RingHom.ker ((r' : A0 →+* AC).comp s0) = Ideal.span {g} := by
    rw [← hker]
    ext γ
    rw [RingHom.mem_ker, RingHom.mem_ker]
    change r (s0 γ) = 0 ↔ sC γ = 0
    rw [hrs]
  have hkey := ker_comp_eq_span s0 hs0 r' g hgker p hps (MvPolynomial.X 1) hk
    (by
      rw [hgy]
      congr 1
      simp [p])
  obtain ⟨e, he⟩ := exists_algEquiv_polynomial (r'.comp p) (hrsurj.comp hps) hkey
  exact ⟨e.toRingEquiv, e.commutes, by simpa [p, r'] using he⟩

/-- Let `K[x, y] → A₀`, `x ↦ x₀`, `y ↦ y₀`, be surjective with kernel contained in `(x)`, and let
`r : A₀ → A_C` be compatible with surjections `s₀ : Γ → A₀` and `s_C : Γ → A_C` such that
`ker s_C = (g)` and `s₀ g = x₀`. Then `A_C` is a polynomial ring over `K` in `r y₀`. -/
theorem bridge_chart_alg' {K : Type u} [Field K] {Γ A0 AC : Type u} [CommRing Γ] [CommRing A0]
    [CommRing AC] (σS : K →+* A0) (σC : K →+* AC) (s0 : Γ →+* A0)
    (hs0 : Function.Surjective s0) (sC : Γ →+* AC) (hsC : Function.Surjective sC)
    (r : A0 →+* AC) (hrs : ∀ γ, r (s0 γ) = sC γ) (hσ : ∀ k, r (σS k) = σC k) (g : Γ)
    (hker : RingHom.ker sC = Ideal.span {g}) (x0 y0 : A0)
    (hs : Function.Surjective (MvPolynomial.eval₂Hom σS ![x0, y0]))
    (hk : RingHom.ker (MvPolynomial.eval₂Hom σS ![x0, y0]) ≤ Ideal.span {MvPolynomial.X 0})
    (hgy : s0 g = x0) :
    ∃ e : K[X] ≃+* AC, (∀ k, e (Polynomial.C k) = σC k) ∧ e X = r y0 := by
  letI : Algebra K A0 := σS.toAlgebra
  letI : Algebra K AC := σC.toAlgebra
  let r' : A0 →ₐ[K] AC := { r with commutes' := hσ }
  let p : MvPolynomial (Fin 2) K →ₐ[K] A0 := MvPolynomial.aeval ![x0, y0]
  have hps : Function.Surjective p := hs
  have hrsurj : Function.Surjective r' := by
    intro c
    obtain ⟨γ, rfl⟩ := hsC c
    exact ⟨s0 γ, hrs γ⟩
  have hgker : RingHom.ker ((r' : A0 →+* AC).comp s0) = Ideal.span {g} := by
    rw [← hker]
    ext γ
    rw [RingHom.mem_ker, RingHom.mem_ker]
    change r (s0 γ) = 0 ↔ sC γ = 0
    rw [hrs]
  have hkey := ker_comp_eq_span s0 hs0 r' g hgker p hps (MvPolynomial.X 0) hk
    (by
      rw [hgy]
      congr 1
      simp [p])
  obtain ⟨e, he⟩ := exists_algEquiv_polynomial' (r'.comp p) (hrsurj.comp hps) hkey
  exact ⟨e.toRingEquiv, e.commutes, by simpa [p, r'] using he⟩

/-- The chart `Spec K[X] ⟶ C` of an affine open with coordinate ring `K[X]`. -/
noncomputable def chartMap {K : Type u} [Field K] {C : Scheme.{u}} {U : C.Opens}
    (hU : IsAffineOpen U) (e : K[X] ≃+* Γ(C, U)) : Spec (.of K[X]) ⟶ C :=
  Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ hU.fromSpec

/-- The chart `chartMap hU e` is an open immersion. -/
instance chartMap_isOpenImmersion {K : Type u} [Field K] {C : Scheme.{u}} {U : C.Opens}
    (hU : IsAffineOpen U) (e : K[X] ≃+* Γ(C, U)) : IsOpenImmersion (chartMap hU e) := by
  unfold chartMap
  haveI : IsIso (CommRingCat.ofHom e.symm.toRingHom) :=
    inferInstanceAs (IsIso e.symm.toCommRingCatIso.hom)
  infer_instance

/-- The image of the chart `chartMap hU e` is `U`. -/
theorem chartMap_opensRange {K : Type u} [Field K] {C : Scheme.{u}} {U : C.Opens}
    (hU : IsAffineOpen U) (e : K[X] ≃+* Γ(C, U)) : (chartMap hU e).opensRange = U := by
  unfold chartMap
  haveI : IsIso (CommRingCat.ofHom e.symm.toRingHom) :=
    inferInstanceAs (IsIso e.symm.toCommRingCatIso.hom)
  rw [Scheme.Hom.opensRange_comp_of_isIso, IsAffineOpen.opensRange_fromSpec]

/-- Morphisms out of the projective line glue from the two charts. -/
theorem exists_hom_projectiveLine {k : Type u} [CommRing k] {C : Scheme.{u}}
    (f₀ f₁ : Spec (.of (Polynomial k)) ⟶ C)
    (h : projectiveLinePuncturedChart k ≫ f₀ =
      (projectiveLineInversionIso k).hom ≫ projectiveLinePuncturedChart k ≫ f₁) :
    ∃ g : projectiveLine k ⟶ C,
      projectiveLineXChart k ≫ g = f₀ ∧ projectiveLineYChart k ≫ g = f₁ := by
  let D := projectiveLineGluingData k
  let F : ∀ i : D.J, Spec (.of (Polynomial k)) ⟶ C := fun i => if i.down then f₁ else f₀
  refine ⟨CategoryTheory.Limits.Multicoequalizer.desc D.toGlueData.diagram _ F ?_,
    Limits.Multicoequalizer.π_desc (I := D.toGlueData.diagram) _ _ _ (projectiveLineXIndex k),
    Limits.Multicoequalizer.π_desc (I := D.toGlueData.diagram) _ _ _ (projectiveLineYIndex k)⟩
  intro a
  rcases a with ⟨⟨i⟩, ⟨j⟩⟩
  change D.f ⟨i⟩ ⟨j⟩ ≫ F ⟨i⟩ = D.t ⟨i⟩ ⟨j⟩ ≫ D.f ⟨j⟩ ⟨i⟩ ≫ F ⟨j⟩
  cases i <;> cases j
  all_goals
    simp only [D, projectiveLineGluingData, CategoryTheory.GlueData.ofGlueData',
        CategoryTheory.GlueData'.f', projectiveLineGluingData', F]
  all_goals simp
  · simpa only [CategoryTheory.eqToHom_comp_iff, CategoryTheory.eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp] using h
  · have h' : (projectiveLineInversionIso k).inv ≫ projectiveLinePuncturedChart k ≫ f₀ =
        projectiveLinePuncturedChart k ≫ f₁ := by
      rw [h, Iso.inv_hom_id_assoc]
    simpa only [CategoryTheory.eqToHom_comp_iff, CategoryTheory.eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp] using h'.symm

/-- The transition relation of the two charts of the projective line. -/
theorem punct_comp_xChart (k : Type u) [CommRing k] :
    projectiveLinePuncturedChart k ≫ projectiveLineXChart k =
      (projectiveLineInversionIso k).hom ≫ projectiveLinePuncturedChart k ≫
        projectiveLineYChart k := by
  let D := projectiveLineGluingData k
  have := (D.glue_condition (projectiveLineXIndex k) (projectiveLineYIndex k)).symm
  simp only [D, projectiveLineGluingData, CategoryTheory.GlueData.ofGlueData',
        CategoryTheory.GlueData'.f', projectiveLineGluingData', projectiveLineXIndex,
        projectiveLineYIndex] at this
  simp at this
  simp only [CategoryTheory.eqToHom_comp_iff, CategoryTheory.eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Category.assoc] at this
  exact this

/-- A morphism from the projective line whose restrictions to the two standard charts are open
immersions `f₀` and `f₁` is injective, provided every point `z` with `f₁ z` in the image of `f₀`
lies in the punctured chart. -/
theorem injective_of_charts {k : Type u} [CommRing k] {C : Scheme.{u}}
    (f₀ f₁ : Spec (.of (Polynomial k)) ⟶ C) [IsOpenImmersion f₀] [IsOpenImmersion f₁]
    (hr : ∀ z w, f₀ w = f₁ z → z ∈ Set.range (projectiveLinePuncturedChart k))
    (g : projectiveLine k ⟶ C)
    (h₀ : projectiveLineXChart k ≫ g = f₀) (h₁ : projectiveLineYChart k ≫ g = f₁) :
    Function.Injective g := by
  have hX : ∀ z, g (projectiveLineXChart k z) = f₀ z := fun z => by
    rw [← h₀]; rfl
  have hY : ∀ z, g (projectiveLineYChart k z) = f₁ z := fun z => by
    rw [← h₁]; rfl
  have hcomm : ∀ w, projectiveLineXChart k (projectiveLinePuncturedChart k w) =
      projectiveLineYChart k (projectiveLinePuncturedChart k
        ((projectiveLineInversionIso k).hom w)) := fun w =>
    congrArg (fun φ => φ w) (punct_comp_xChart k)
  have hcover : ∀ a : projectiveLine k, (∃ z, projectiveLineXChart k z = a) ∨
      ∃ z, projectiveLineYChart k z = a := fun a => by
    obtain ⟨i, z, rfl⟩ := (projectiveLineGluingData k).openCover.exists_eq a
    obtain ⟨i⟩ := i
    cases i
    · exact Or.inl ⟨z, rfl⟩
    · exact Or.inr ⟨z, rfl⟩
  have hinv : ∀ w, (projectiveLineInversionIso k).hom ((projectiveLineInversionIso k).inv w) = w :=
    fun w => congrArg (fun φ => φ w) (projectiveLineInversionIso k).inv_hom_id
  have hmix : ∀ z z', f₀ z = f₁ z' → projectiveLineXChart k z = projectiveLineYChart k z' := by
    intro z z' hzz
    obtain ⟨w, rfl⟩ := hr z' z hzz
    have e := hcomm ((projectiveLineInversionIso k).inv w)
    rw [hinv] at e
    rw [← e]
    have : f₀ z = f₀ (projectiveLinePuncturedChart k ((projectiveLineInversionIso k).inv w)) := by
      rw [hzz, ← hY, ← e, hX]
    rw [(f₀.isOpenEmbedding.injective) this]
  intro a b hab
  rcases hcover a with ⟨z, rfl⟩ | ⟨z, rfl⟩ <;> rcases hcover b with ⟨z', rfl⟩ | ⟨z', rfl⟩
  · rw [hX, hX] at hab
    rw [f₀.isOpenEmbedding.injective hab]
  · rw [hX, hY] at hab
    exact hmix z z' hab
  · rw [hY, hX] at hab
    exact (hmix z' z hab.symm).symm
  · rw [hY, hY] at hab
    rw [f₁.isOpenEmbedding.injective hab]

/-- A gluing of two open charts covering the target is an isomorphism. -/
theorem isIso_of_charts {k : Type u} [CommRing k] {C : Scheme.{u}}
    (f₀ f₁ : Spec (.of (Polynomial k)) ⟶ C) [IsOpenImmersion f₀] [IsOpenImmersion f₁]
    (hcov : f₀.opensRange ⊔ f₁.opensRange = ⊤)
    (hr : ∀ z w, f₀ w = f₁ z → z ∈ Set.range (projectiveLinePuncturedChart k))
    (g : projectiveLine k ⟶ C)
    (h₀ : projectiveLineXChart k ≫ g = f₀) (h₁ : projectiveLineYChart k ≫ g = f₁) :
    IsIso g := by
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨?_, ?_⟩
  · refine IsOpenImmersion.of_openCover_source g (projectiveLineGluingData k).openCover
      (injective_of_charts f₀ f₁ hr g h₀ h₁) ?_
    intro i
    obtain ⟨i⟩ := i
    cases i
    · change IsOpenImmersion (projectiveLineXChart k ≫ g)
      rw [h₀]; infer_instance
    · change IsOpenImmersion (projectiveLineYChart k ≫ g)
      rw [h₁]; infer_instance
  · constructor
    intro c
    have hc : c ∈ (f₀.opensRange ⊔ f₁.opensRange : C.Opens) := by rw [hcov]; trivial
    rcases hc with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · exact ⟨projectiveLineXChart k z, by rw [← h₀]; rfl⟩
    · exact ⟨projectiveLineYChart k z, by rw [← h₁]; rfl⟩

/-- The two coordinate charts of a line with `x y = 1` on the overlap induce one ring map from the
overlap ring to the Laurent polynomials, restricting to the standard maps on both charts. -/
theorem exists_laurent_compat {K : Type u} [Field K] {A B R : Type u} [CommRing A] [CommRing B]
    [CommRing R] [Algebra K A] [Algebra K B] [Algebra K R] [Algebra A R] [Algebra B R]
    [IsScalarTower K A R] [IsScalarTower K B R]
    (eA : A ≃ₐ[K] K[X]) (eB : B ≃ₐ[K] K[X])
    [IsLocalization.Away (eA.symm X) R]
    (hxy : algebraMap A R (eA.symm X) * algebraMap B R (eB.symm X) = 1) :
    ∃ θ : R →ₐ[K] LaurentPolynomial K,
      (∀ a, θ (algebraMap A R a) = Polynomial.toLaurent (eA a)) ∧
      (∀ b, θ (algebraMap B R b) = LaurentPolynomial.invert (Polynomial.toLaurent (eB b))) := by
  let f : A →ₐ[K] LaurentPolynomial K := (Polynomial.toLaurentAlg (R := K)).comp eA.toAlgHom
  have hf : ∀ y : Submonoid.powers (eA.symm X), IsUnit (f y) := by
    rintro ⟨_, n, rfl⟩
    simp only [f, AlgHom.comp_apply, map_pow]
    refine IsUnit.pow _ ?_
    simpa using isUnit_T 1
  let θ : R →ₐ[K] LaurentPolynomial K := IsLocalization.liftAlgHom hf
  have hθA : ∀ a, θ (algebraMap A R a) = Polynomial.toLaurent (eA a) := fun a => by
    have h1 : θ (algebraMap A R a) = f a := IsLocalization.lift_eq (S := R) _ a
    rw [h1]
    simp [f]
  refine ⟨θ, hθA, fun b => ?_⟩
  have hX : θ (algebraMap B R (eB.symm X)) = (LaurentPolynomial.T (-1) : LaurentPolynomial K) := by
    have h1 := congrArg θ hxy
    rw [map_mul, hθA, map_one, AlgEquiv.apply_symm_apply, Polynomial.toLaurent_X] at h1
    have h2 : (LaurentPolynomial.T 1 : LaurentPolynomial K) * LaurentPolynomial.T (-1) = 1 := by
      rw [← LaurentPolynomial.T_add]; simp
    exact ((isUnit_T (R := K) 1).mul_right_inj).1 (h1.trans h2.symm)
  let φ₁ : B →ₐ[K] LaurentPolynomial K := θ.comp (IsScalarTower.toAlgHom K B R)
  let φ₂ : B →ₐ[K] LaurentPolynomial K :=
    ((LaurentPolynomial.invert (R := K)).toAlgHom.comp
      (Polynomial.toLaurentAlg (R := K))).comp eB.toAlgHom
  have hφ : φ₁.comp eB.symm.toAlgHom = φ₂.comp eB.symm.toAlgHom := by
    refine Polynomial.algHom_ext ?_
    simp only [φ₁, φ₂, AlgHom.comp_apply]
    have e1 : θ ((IsScalarTower.toAlgHom K B R) (eB.symm X)) = LaurentPolynomial.T (-1) := hX
    refine e1.trans ?_
    simp [LaurentPolynomial.invert_T]
  simpa [φ₁, φ₂] using congrArg (fun φ => φ (eB b)) hφ

/-- If `θ ∘ res = ψ ∘ e⁻¹` on the sections over `U`, then `Spec ψ ≫ chartMap hU e` is
`Spec θ ≫ hW.fromSpec`. -/
theorem chartMap_comp {K : Type u} [Field K] {C : Scheme.{u}} {U W : C.Opens}
    (hU : IsAffineOpen U) (hW : IsAffineOpen W) (i : op U ⟶ op W) (e : K[X] ≃+* Γ(C, U))
    {R : CommRingCat.{u}} (θ : Γ(C, W) ⟶ R) (ψ : CommRingCat.of K[X] ⟶ R)
    (h : ∀ a, θ.hom (C.presheaf.map i a) = ψ.hom (e.symm a)) :
    Spec.map ψ ≫ chartMap hU e = Spec.map θ ≫ hW.fromSpec := by
  unfold chartMap
  rw [← Category.assoc, ← Spec.map_comp]
  have : CommRingCat.ofHom e.symm.toRingHom ≫ ψ = C.presheaf.map i ≫ θ :=
    CommRingCat.hom_ext (RingHom.ext fun a => (h a).symm)
  rw [this, Spec.map_comp, Category.assoc, IsAffineOpen.map_fromSpec hU hW i]

/-- Let `e₀` and `e₁` be `K`-linear identifications of the sections over `U₀` and `U₁` with `K[X]`,
with `U₀ ⊓ U₁ = D(e₀ X)` and `e₀ X · e₁ X = 1` there. Then there is a ring map
`Γ(C, U₀ ⊓ U₁) → K[T, T⁻¹]` sending the restriction of `a` to `e₀⁻¹ a` and the restriction of `b`
to the inversion of `e₁⁻¹ b`. -/
theorem exists_theta {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (.of K))
    {U0 U1 : C.Opens} (hU0 : IsAffineOpen U0)
    (e0 : K[X] ≃+* Γ(C, U0)) (e1 : K[X] ≃+* Γ(C, U1))
    (he0 : ∀ k, e0 (Polynomial.C k) = ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appLE ⊤ U0 (by simp)).hom k)
    (he1 : ∀ k, e1 (Polynomial.C k) = ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appLE ⊤ U1 (by simp)).hom k)
    (hW0 : C.basicOpen (e0 X) = U0 ⊓ U1)
    (hxy : C.presheaf.map (homOfLE (inf_le_left : U0 ⊓ U1 ≤ U0)).op (e0 X) *
      C.presheaf.map (homOfLE (inf_le_right : U0 ⊓ U1 ≤ U1)).op (e1 X) = 1) :
    ∃ θ : Γ(C, U0 ⊓ U1) →+* LaurentPolynomial K,
      (∀ a, θ (C.presheaf.map (homOfLE (inf_le_left : U0 ⊓ U1 ≤ U0)).op a) =
        Polynomial.toLaurent (e0.symm a)) ∧
      (∀ b, θ (C.presheaf.map (homOfLE (inf_le_right : U0 ⊓ U1 ≤ U1)).op b) =
        LaurentPolynomial.invert (Polynomial.toLaurent (e1.symm b))) := by
  letI algA : Algebra K Γ(C, U0) := (((Scheme.ΓSpecIso (.of K)).inv ≫ c.appLE ⊤ U0 (by simp)).hom).toAlgebra
  letI algB : Algebra K Γ(C, U1) := (((Scheme.ΓSpecIso (.of K)).inv ≫ c.appLE ⊤ U1 (by simp)).hom).toAlgebra
  letI algR : Algebra K Γ(C, U0 ⊓ U1) :=
    (((Scheme.ΓSpecIso (.of K)).inv ≫ c.appLE ⊤ (U0 ⊓ U1) (by simp)).hom).toAlgebra
  letI algAR : Algebra Γ(C, U0) Γ(C, U0 ⊓ U1) :=
    (C.presheaf.map (homOfLE (inf_le_left : U0 ⊓ U1 ≤ U0)).op).hom.toAlgebra
  letI algBR : Algebra Γ(C, U1) Γ(C, U0 ⊓ U1) :=
    (C.presheaf.map (homOfLE (inf_le_right : U0 ⊓ U1 ≤ U1)).op).hom.toAlgebra
  haveI : IsScalarTower K Γ(C, U0) Γ(C, U0 ⊓ U1) :=
    IsScalarTower.of_algebraMap_eq fun k => (map_constants_restrict c U0 (U0 ⊓ U1) inf_le_left k).symm
  haveI : IsScalarTower K Γ(C, U1) Γ(C, U0 ⊓ U1) :=
    IsScalarTower.of_algebraMap_eq fun k => (map_constants_restrict c U1 (U0 ⊓ U1) inf_le_right k).symm
  let eA : Γ(C, U0) ≃ₐ[K] K[X] := AlgEquiv.ofRingEquiv (f := e0.symm) fun k => by
    have h := he0 k
    have h' : algebraMap K Γ(C, U0) k = e0 (Polynomial.C k) := h.symm
    rw [h', e0.symm_apply_apply]
    rfl
  let eB : Γ(C, U1) ≃ₐ[K] K[X] := AlgEquiv.ofRingEquiv (f := e1.symm) fun k => by
    have h := he1 k
    have h' : algebraMap K Γ(C, U1) k = e1 (Polynomial.C k) := h.symm
    rw [h', e1.symm_apply_apply]
    rfl
  haveI : IsLocalization.Away (eA.symm X) Γ(C, U0 ⊓ U1) :=
    hU0.isLocalization_of_eq_basicOpen (e0 X) (homOfLE (inf_le_left : U0 ⊓ U1 ≤ U0)) hW0.symm
  obtain ⟨θ, h1, h2⟩ := exists_laurent_compat eA eB hxy
  exact ⟨θ.toRingHom, h1, h2⟩

/-- Under the hypotheses of `exists_theta`, the charts `chartMap hU0 e0` and `chartMap hU1 e1`
satisfy the gluing relation of the projective line on the punctured chart. -/
theorem compat_charts {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (.of K))
    {U0 U1 : C.Opens} (hU0 : IsAffineOpen U0) (hU1 : IsAffineOpen U1)
    (e0 : K[X] ≃+* Γ(C, U0)) (e1 : K[X] ≃+* Γ(C, U1))
    (he0 : ∀ k, e0 (Polynomial.C k) = ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appLE ⊤ U0 (by simp)).hom k)
    (he1 : ∀ k, e1 (Polynomial.C k) = ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appLE ⊤ U1 (by simp)).hom k)
    (hW0 : C.basicOpen (e0 X) = U0 ⊓ U1)
    (hxy : C.presheaf.map (homOfLE (inf_le_left : U0 ⊓ U1 ≤ U0)).op (e0 X) *
      C.presheaf.map (homOfLE (inf_le_right : U0 ⊓ U1 ≤ U1)).op (e1 X) = 1) :
    projectiveLinePuncturedChart K ≫ chartMap hU0 e0 =
      (projectiveLineInversionIso K).hom ≫ projectiveLinePuncturedChart K ≫ chartMap hU1 e1 := by
  have hW : IsAffineOpen (U0 ⊓ U1) := hW0 ▸ hU0.basicOpen _
  obtain ⟨θ, h1, h2⟩ := exists_theta c hU0 e0 e1 he0 he1 hW0 hxy
  have m1 := chartMap_comp hU0 hW (homOfLE (inf_le_left : U0 ⊓ U1 ≤ U0)).op e0
    (CommRingCat.ofHom θ) (CommRingCat.ofHom (Polynomial.toLaurent (R := K))) h1
  have m2 := chartMap_comp hU1 hW (homOfLE (inf_le_right : U0 ⊓ U1 ≤ U1)).op e1
    (CommRingCat.ofHom θ)
    (CommRingCat.ofHom (Polynomial.toLaurent (R := K)) ≫
      CommRingCat.ofHom (LaurentPolynomial.invert (R := K)).toRingEquiv.toRingHom) h2
  have hinv : (projectiveLineInversionIso K).hom =
      Spec.map (CommRingCat.ofHom (LaurentPolynomial.invert (R := K)).toRingEquiv.toRingHom) := rfl
  unfold projectiveLinePuncturedChart
  rw [hinv, ← Category.assoc, ← Spec.map_comp, m1, m2]

/-- A point `z` of `Spec K[X]` whose image under `chartMap hU1 e1` lies in `D(e1 X)` lies in the
image of the punctured chart. -/
theorem mem_range_punct_of_chartMap {K : Type u} [Field K] {C : Scheme.{u}}
    {U1 : C.Opens} (hU1 : IsAffineOpen U1) (e1 : K[X] ≃+* Γ(C, U1))
    (z : Spec (.of K[X])) (hz : chartMap hU1 e1 z ∈ C.basicOpen (e1 X)) :
    z ∈ Set.range (projectiveLinePuncturedChart K) := by
  have h1 : (Spec.map (CommRingCat.ofHom e1.symm.toRingHom)) z ∈
      hU1.fromSpec ⁻¹ᵁ C.basicOpen (e1 X) := hz
  rw [IsAffineOpen.fromSpec_preimage_basicOpen] at h1
  have h2 : (X : K[X]) ∉ z.asIdeal := by
    intro hX
    refine (PrimeSpectrum.mem_basicOpen _ _).1 h1 ?_
    change e1 X ∈ Ideal.comap e1.symm.toRingHom z.asIdeal
    rw [Ideal.mem_comap]
    simpa using hX
  have hr := PrimeSpectrum.localization_away_comap_range K[T;T⁻¹] (X : K[X])
  have hz' : z ∈ Set.range (PrimeSpectrum.comap (algebraMap K[X] K[T;T⁻¹])) := by
    rw [hr]; exact h2
  obtain ⟨w, hw⟩ := hz'
  exact ⟨w, hw⟩

/-- A `K`-scheme covered by two affine opens `U₀`, `U₁` with `K`-linear coordinate rings `K[X]`,
such that `U₀ ⊓ U₁ = D(e₀ X) = D(e₁ X)` and `e₀ X · e₁ X = 1` there, is isomorphic to the
projective line by a morphism restricting to `chartMap hU0 e0` and `chartMap hU1 e1` on the two
charts. -/
theorem exists_iso_projectiveLine {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (.of K))
    {U0 U1 : C.Opens} (hU0 : IsAffineOpen U0) (hU1 : IsAffineOpen U1)
    (e0 : K[X] ≃+* Γ(C, U0)) (e1 : K[X] ≃+* Γ(C, U1))
    (he0 : ∀ k, e0 (Polynomial.C k) = ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appLE ⊤ U0 (by simp)).hom k)
    (he1 : ∀ k, e1 (Polynomial.C k) = ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appLE ⊤ U1 (by simp)).hom k)
    (hcov : U0 ⊔ U1 = ⊤)
    (hW0 : C.basicOpen (e0 X) = U0 ⊓ U1) (hW1 : C.basicOpen (e1 X) = U0 ⊓ U1)
    (hxy : C.presheaf.map (homOfLE (inf_le_left : U0 ⊓ U1 ≤ U0)).op (e0 X) *
      C.presheaf.map (homOfLE (inf_le_right : U0 ⊓ U1 ≤ U1)).op (e1 X) = 1) :
    ∃ g : projectiveLine K ⟶ C, IsIso g ∧ projectiveLineXChart K ≫ g = chartMap hU0 e0 ∧
      projectiveLineYChart K ≫ g = chartMap hU1 e1 := by
  obtain ⟨g, hg0, hg1⟩ := exists_hom_projectiveLine (chartMap hU0 e0) (chartMap hU1 e1)
    (compat_charts c hU0 hU1 e0 e1 he0 he1 hW0 hxy)
  refine ⟨g, ?_, hg0, hg1⟩
  refine isIso_of_charts (chartMap hU0 e0) (chartMap hU1 e1) ?_ ?_ g hg0 hg1
  · rw [chartMap_opensRange, chartMap_opensRange, hcov]
  · intro z w hzw
    have h0 : chartMap hU1 e1 z ∈ U0 := by
      rw [← hzw]
      have : chartMap hU0 e0 w ∈ (chartMap hU0 e0).opensRange := ⟨w, rfl⟩
      rwa [chartMap_opensRange] at this
    have h1 : chartMap hU1 e1 z ∈ U1 := by
      have : chartMap hU1 e1 z ∈ (chartMap hU1 e1).opensRange := ⟨z, rfl⟩
      rwa [chartMap_opensRange] at this
    refine mem_range_punct_of_chartMap hU1 e1 z ?_
    rw [hW1]
    exact ⟨h0, h1⟩

/-- For `K`-linear `e`, the chart `chartMap hU e` followed by the structure morphism `c` is
`projectiveLineAffineStructureMorphism K`. -/
theorem chartMap_comp_base {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (.of K))
    {U : C.Opens} (hU : IsAffineOpen U) (e : K[X] ≃+* Γ(C, U))
    (he : ∀ k, e (Polynomial.C k) =
      ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appLE ⊤ U (by simp)).hom k) :
    chartMap hU e ≫ c = projectiveLineAffineStructureMorphism K := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec c (isAffineOpen_top (Spec (.of K))) hU
    (by simp : U ≤ c ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  unfold chartMap projectiveLineAffineStructureMorphism
  rw [Category.assoc, ← h, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun k => ?_)
  change e.symm (((Scheme.ΓSpecIso (.of K)).inv ≫ c.appLE ⊤ U (by simp)).hom k) = Polynomial.C k
  rw [← he k, e.symm_apply_apply]

/-- A morphism from the projective line restricting to `K`-linear charts is a morphism over
`Spec K`. -/
theorem comp_base_of_charts {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (.of K))
    {U0 U1 : C.Opens} (hU0 : IsAffineOpen U0) (hU1 : IsAffineOpen U1)
    (e0 : K[X] ≃+* Γ(C, U0)) (e1 : K[X] ≃+* Γ(C, U1))
    (he0 : ∀ k, e0 (Polynomial.C k) = ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appLE ⊤ U0 (by simp)).hom k)
    (he1 : ∀ k, e1 (Polynomial.C k) = ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appLE ⊤ U1 (by simp)).hom k)
    (g : projectiveLine K ⟶ C) (hg0 : projectiveLineXChart K ≫ g = chartMap hU0 e0)
    (hg1 : projectiveLineYChart K ≫ g = chartMap hU1 e1) :
    g ≫ c = projectiveLine K ↘ Spec (.of K) := by
  refine projectiveLine_hom_ext ?_ ?_
  · rw [← Category.assoc, hg0, chartMap_comp_base c hU0 e0 he0,
      projectiveLineXChart_comp_structureMorphism]
  · rw [← Category.assoc, hg1, chartMap_comp_base c hU1 e1 he1,
      projectiveLineYChart_comp_structureMorphism]

/-- The structure constants `K → Γ(Z, Z ∩ U)` of a closed subscheme. -/
noncomputable abbrev sigmaSub {K : Type u} [Field K] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of K))
    (Z : Y.IdealSheafData) (U : Y.Opens) : K →+* Γ(Z.subscheme, Z.subschemeι ⁻¹ᵁ U) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫
    (Z.subschemeι ≫ sY).appLE ⊤ (Z.subschemeι ⁻¹ᵁ U) le_top).hom

/-- The structure constants `sigmaSub` commute with restriction. -/
theorem sigmaSub_restrict {K : Type u} [Field K] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of K))
    (Z : Y.IdealSheafData) {U U' : Y.Opens} (h : U' ≤ U) (k : K) :
    (Z.subscheme.presheaf.map (homOfLE (Scheme.Hom.preimage_mono _ h)).op).hom
      (sigmaSub sY Z U k) = sigmaSub sY Z U' k :=
  map_constants_restrict (Z.subschemeι ≫ sY) _ _ _ k

/-- `inclSections` maps the structure constants of `I` to those of `Ej`. -/
theorem inclSections_sigma {K : Type u} [Field K] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of K))
    {I Ej : Y.IdealSheafData} (hIE : I ≤ Ej) (U : Y.Opens) (k : K) :
    inclSections hIE U (sigmaSub sY I U k) = sigmaSub sY Ej U k :=
  map_constants_hom (Ej.subschemeι ≫ sY) (I.subschemeι ≫ sY) (Scheme.IdealSheafData.inclusion hIE)
    (by rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]) _ _ _ k

/-- `inclSections` commutes with restriction. -/
theorem inclSections_restrict {Y : Scheme.{u}} {I Ej : Y.IdealSheafData} (hIE : I ≤ Ej)
    {U U' : Y.Opens} (h : U' ≤ U) (a : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U)) :
    (Ej.subscheme.presheaf.map (homOfLE (Scheme.Hom.preimage_mono _ h)).op).hom
      (inclSections hIE U a) =
    inclSections hIE U' ((I.subscheme.presheaf.map (homOfLE (Scheme.Hom.preimage_mono _ h)).op).hom a) := by
  unfold inclSections
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map,
    Scheme.Hom.map_appLE]

/-- If `x₀`, `y₀` generate the sections of `I.subscheme` over `V` as a `K`-algebra, with relations
contained in `(y)`, and the kernel of `inclSections hIE V` is `(y₀)`, then the sections of
`Ej.subscheme` over `V` form a polynomial ring over `K` in the image of `x₀`. -/
theorem bridge_chart_ker {K : Type u} [Field K] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of K))
    (I Ej : Y.IdealSheafData) (hIE : I ≤ Ej) (V : Y.Opens)
    (hV : IsAffineOpen (I.subschemeι ⁻¹ᵁ V))
    (x0 y0 : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V))
    (hs : Function.Surjective (MvPolynomial.eval₂Hom
      ((Scheme.ΓSpecIso (.of K)).inv ≫ (I.subschemeι ≫ sY).appLE ⊤ (I.subschemeι ⁻¹ᵁ V) le_top).hom
      ![x0, y0]))
    (hk : RingHom.ker (MvPolynomial.eval₂Hom
      ((Scheme.ΓSpecIso (.of K)).inv ≫ (I.subschemeι ≫ sY).appLE ⊤ (I.subschemeι ⁻¹ᵁ V) le_top).hom
      ![x0, y0]) ≤ Ideal.span {MvPolynomial.X 1})
    (hy : RingHom.ker (inclSections hIE V) = Ideal.span {y0}) :
    ∃ e : K[X] ≃+* Γ(Ej.subscheme, Ej.subschemeι ⁻¹ᵁ V),
      (∀ k, e (Polynomial.C k) =
        ((Scheme.ΓSpecIso (.of K)).inv ≫
          (Ej.subschemeι ≫ sY).appLE ⊤ (Ej.subschemeι ⁻¹ᵁ V) le_top).hom k) ∧
      e X = inclSections hIE V x0 := by
  exact bridge_chart_alg _ _ (RingHom.id _) (fun a => ⟨a, rfl⟩) (inclSections hIE V)
    (inclSections_surjective hIE V hV) (inclSections hIE V) (fun _ => rfl) (inclSections_sigma sY hIE V) y0
    (by rw [hy]) x0 y0 hs hk rfl

/-- If `x₀`, `y₀` generate the sections of `I.subscheme` over `V` as a `K`-algebra, with relations
contained in `(x)`, and the kernel of `inclSections hIE V` is `(x₀)`, then the sections of
`Ej.subscheme` over `V` form a polynomial ring over `K` in the image of `y₀`. -/
theorem bridge_chart_ker' {K : Type u} [Field K] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of K))
    (I Ej : Y.IdealSheafData) (hIE : I ≤ Ej) (V : Y.Opens)
    (hV : IsAffineOpen (I.subschemeι ⁻¹ᵁ V))
    (x0 y0 : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V))
    (hs : Function.Surjective (MvPolynomial.eval₂Hom
      ((Scheme.ΓSpecIso (.of K)).inv ≫ (I.subschemeι ≫ sY).appLE ⊤ (I.subschemeι ⁻¹ᵁ V) le_top).hom
      ![x0, y0]))
    (hk : RingHom.ker (MvPolynomial.eval₂Hom
      ((Scheme.ΓSpecIso (.of K)).inv ≫ (I.subschemeι ≫ sY).appLE ⊤ (I.subschemeι ⁻¹ᵁ V) le_top).hom
      ![x0, y0]) ≤ Ideal.span {MvPolynomial.X 0})
    (hx : RingHom.ker (inclSections hIE V) = Ideal.span {x0}) :
    ∃ e : K[X] ≃+* Γ(Ej.subscheme, Ej.subschemeι ⁻¹ᵁ V),
      (∀ k, e (Polynomial.C k) =
        ((Scheme.ΓSpecIso (.of K)).inv ≫
          (Ej.subschemeι ≫ sY).appLE ⊤ (Ej.subschemeι ⁻¹ᵁ V) le_top).hom k) ∧
      e X = inclSections hIE V y0 := by
  exact bridge_chart_alg' _ _ (RingHom.id _) (fun a => ⟨a, rfl⟩) (inclSections hIE V)
    (inclSections_surjective hIE V hV) (inclSections hIE V) (fun _ => rfl) (inclSections_sigma sY hIE V) x0
    (by rw [hx]) x0 y0 hs hk rfl

/-- Let `xa`, `ya` and `xb`, `yb` generate the sections of `I.subscheme` over `V₀` and `V₁` as in
`bridge_chart_ker` and `bridge_chart_ker'`, with `Ej` cut out by `ya` and `xb`, with
`D(xa) = D(yb)` the preimage of `V₀ ⊓ V₁` and `yb · xa = d ≠ 0` there. If `V₀ ∪ V₁` contains the
support of `Ej`, then `Ej.subscheme` is isomorphic over `K` to the projective line, with charts
`e₀`, `e₁` sending `X` to the images of `xa` and `d⁻¹ yb`. -/
theorem exists_epsilon_data' {K : Type u} [Field K] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of K))
    (I Ej : Y.IdealSheafData) (hIE : I ≤ Ej) (V0 V1 : Y.Opens)
    (hA0 : IsAffineOpen (I.subschemeι ⁻¹ᵁ V0)) (hA1 : IsAffineOpen (I.subschemeι ⁻¹ᵁ V1))
    (xa ya : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V0)) (xb yb : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V1))
    (hsa : Function.Surjective (MvPolynomial.eval₂Hom (sigmaSub sY I V0) ![xa, ya]))
    (hka : RingHom.ker (MvPolynomial.eval₂Hom (sigmaSub sY I V0) ![xa, ya]) ≤
      Ideal.span {MvPolynomial.X 1})
    (hsb : Function.Surjective (MvPolynomial.eval₂Hom (sigmaSub sY I V1) ![xb, yb]))
    (hkb : RingHom.ker (MvPolynomial.eval₂Hom (sigmaSub sY I V1) ![xb, yb]) ≤
      Ideal.span {MvPolynomial.X 0})
    (hy0 : RingHom.ker (inclSections hIE V0) = Ideal.span {ya})
    (hx1 : RingHom.ker (inclSections hIE V1) = Ideal.span {xb})
    (hov0 : I.subschemeι ⁻¹ᵁ (V0 ⊓ V1) = I.subscheme.basicOpen xa)
    (hov1 : I.subschemeι ⁻¹ᵁ (V0 ⊓ V1) = I.subscheme.basicOpen yb)
    (d : K) (hd : d ≠ 0)
    (hxy : I.subscheme.presheaf.map (homOfLE (Scheme.Hom.preimage_mono _
        (inf_le_right : V0 ⊓ V1 ≤ V1))).op yb *
      I.subscheme.presheaf.map (homOfLE (Scheme.Hom.preimage_mono _
        (inf_le_left : V0 ⊓ V1 ≤ V0))).op xa = sigmaSub sY I (V0 ⊓ V1) d)
    (hcov : (Ej.support : Set Y) ⊆ (V0 : Set Y) ∪ (V1 : Set Y)) :
    ∃ (g : projectiveLine K ⟶ Ej.subscheme)
      (hU0 : IsAffineOpen (Ej.subschemeι ⁻¹ᵁ V0)) (hU1 : IsAffineOpen (Ej.subschemeι ⁻¹ᵁ V1))
      (e0 : K[X] ≃+* Γ(Ej.subscheme, Ej.subschemeι ⁻¹ᵁ V0))
      (e1 : K[X] ≃+* Γ(Ej.subscheme, Ej.subschemeι ⁻¹ᵁ V1)),
      IsIso g ∧ g ≫ Ej.subschemeι ≫ sY = (projectiveLine K ↘ Spec (.of K)) ∧
      projectiveLineXChart K ≫ g = chartMap hU0 e0 ∧
      projectiveLineYChart K ≫ g = chartMap hU1 e1 ∧
      e0 X = inclSections hIE V0 xa ∧
      e1 X = sigmaSub sY Ej V1 d⁻¹ * inclSections hIE V1 yb ∧
      (∀ k, e0 (Polynomial.C k) = sigmaSub sY Ej V0 k) ∧
      (∀ k, e1 (Polynomial.C k) = sigmaSub sY Ej V1 k) := by
  obtain ⟨e0, he0c, he0X⟩ := bridge_chart_ker sY I Ej hIE V0 hA0 xa ya hsa hka hy0
  obtain ⟨e1', he1c, he1X⟩ := bridge_chart_ker' sY I Ej hIE V1 hA1 xb yb hsb hkb hx1
  haveI : Invertible d := invertibleOfNonzero hd
  let sc : K[X] ≃+* K[X] := (Polynomial.algEquivCMulXAddC (⅟d) 0).toRingEquiv
  let e1 : K[X] ≃+* Γ(Ej.subscheme, Ej.subschemeι ⁻¹ᵁ V1) := sc.trans e1'
  have hscX : sc (Polynomial.X : K[X]) = Polynomial.C (⅟d) * (Polynomial.X : K[X]) := by simp [sc]
  have hscC : ∀ k, sc (Polynomial.C k) = Polynomial.C k := fun k => by simp [sc]
  have he1X' : e1 X = sigmaSub sY Ej V1 d⁻¹ * inclSections hIE V1 yb := by
    change e1' (sc X) = _
    rw [hscX, map_mul, he1X, he1c, invOf_eq_inv]
  have he1c' : ∀ k, e1 (Polynomial.C k) = sigmaSub sY Ej V1 k := fun k => by
    change e1' (sc (Polynomial.C k)) = _
    rw [hscC, he1c]
  have hU0 : IsAffineOpen (Ej.subschemeι ⁻¹ᵁ V0) := isAffineOpen_of_closedImmersion_affine hIE V0 hA0
  have hU1 : IsAffineOpen (Ej.subschemeι ⁻¹ᵁ V1) := isAffineOpen_of_closedImmersion_affine hIE V1 hA1
  have hcov' : Ej.subschemeι ⁻¹ᵁ V0 ⊔ Ej.subschemeι ⁻¹ᵁ V1 = ⊤ := by
    refine top_unique fun p _ => ?_
    have : Ej.subschemeι p ∈ (Ej.support : Set Y) := by
      rw [← Ej.range_subschemeι]; exact ⟨p, rfl⟩
    rcases hcov this with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hpre : ∀ A : Y.Opens, (Scheme.IdealSheafData.inclusion hIE) ⁻¹ᵁ (I.subschemeι ⁻¹ᵁ A) =
      Ej.subschemeι ⁻¹ᵁ A := fun A => by
    rw [← Scheme.Hom.comp_preimage, Scheme.IdealSheafData.inclusion_subschemeι]
  have hinf : Ej.subschemeι ⁻¹ᵁ (V0 ⊓ V1) = Ej.subschemeι ⁻¹ᵁ V0 ⊓ Ej.subschemeι ⁻¹ᵁ V1 := rfl
  have hW0 : Ej.subscheme.basicOpen (e0 X) =
      Ej.subschemeι ⁻¹ᵁ V0 ⊓ Ej.subschemeι ⁻¹ᵁ V1 := by
    rw [he0X, Scheme.basicOpen_appLE, ← hov0, hpre, hinf]
    simp
  have hW1 : Ej.subscheme.basicOpen (e1 X) =
      Ej.subschemeι ⁻¹ᵁ V0 ⊓ Ej.subschemeι ⁻¹ᵁ V1 := by
    have hu : IsUnit (sigmaSub sY Ej V1 d⁻¹) :=
      (isUnit_iff_ne_zero.2 (inv_ne_zero hd)).map _
    rw [he1X', Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ hu]
    unfold inclSections
    rw [Scheme.basicOpen_appLE, ← hov1, hpre, hinf]
    simp
  have hxyC : Ej.subscheme.presheaf.map (homOfLE (inf_le_left :
        Ej.subschemeι ⁻¹ᵁ V0 ⊓ Ej.subschemeι ⁻¹ᵁ V1 ≤ Ej.subschemeι ⁻¹ᵁ V0)).op (e0 X) *
      Ej.subscheme.presheaf.map (homOfLE (inf_le_right :
        Ej.subschemeι ⁻¹ᵁ V0 ⊓ Ej.subschemeι ⁻¹ᵁ V1 ≤ Ej.subschemeι ⁻¹ᵁ V1)).op (e1 X) = 1 := by
    have r0 := inclSections_restrict hIE (inf_le_left : V0 ⊓ V1 ≤ V0) xa
    have r1 := inclSections_restrict hIE (inf_le_right : V0 ⊓ V1 ≤ V1) yb
    have s1 := sigmaSub_restrict sY Ej (inf_le_right : V0 ⊓ V1 ≤ V1) d⁻¹
    have s2 := inclSections_sigma sY hIE (V0 ⊓ V1) d
    rw [he0X, he1X', map_mul]
    erw [r0, s1, r1]
    calc inclSections hIE (V0 ⊓ V1) ((I.subscheme.presheaf.map (homOfLE (Scheme.Hom.preimage_mono _
            (inf_le_left : V0 ⊓ V1 ≤ V0))).op).hom xa) *
          (sigmaSub sY Ej (V0 ⊓ V1) d⁻¹ * inclSections hIE (V0 ⊓ V1)
            ((I.subscheme.presheaf.map (homOfLE (Scheme.Hom.preimage_mono _
              (inf_le_right : V0 ⊓ V1 ≤ V1))).op).hom yb))
        = sigmaSub sY Ej (V0 ⊓ V1) d⁻¹ * inclSections hIE (V0 ⊓ V1)
            (((I.subscheme.presheaf.map (homOfLE (Scheme.Hom.preimage_mono _
              (inf_le_right : V0 ⊓ V1 ≤ V1))).op).hom yb) *
            ((I.subscheme.presheaf.map (homOfLE (Scheme.Hom.preimage_mono _
              (inf_le_left : V0 ⊓ V1 ≤ V0))).op).hom xa)) := by
          rw [map_mul]; ring
      _ = sigmaSub sY Ej (V0 ⊓ V1) d⁻¹ * sigmaSub sY Ej (V0 ⊓ V1) d := by
          rw [hxy, s2]
      _ = 1 := by
          rw [← map_mul, inv_mul_cancel₀ hd, map_one]
  obtain ⟨g, hgi, hg0, hg1⟩ := exists_iso_projectiveLine (Ej.subschemeι ≫ sY) hU0 hU1 e0 e1
    he0c he1c' hcov' hW0 hW1 hxyC
  exact ⟨g, hU0, hU1, e0, e1, hgi, comp_base_of_charts _ hU0 hU1 e0 e1 he0c he1c' g hg0 hg1,
    hg0, hg1, he0X, he1X', he0c, he1c'⟩

section AwayCoord

/-- The coordinate-ring identification `Γ(Proj, D₊(f)) → (A_f)₀` by restriction along `awayι`. -/
noncomputable def awayCoord {A : Type u} [CommRing A] {σ : Type*} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (f : A) (f_deg : f ∈ 𝒜 1) :
    Γ(AlgebraicGeometry.Proj 𝒜, Proj.basicOpen 𝒜 f) →+* HomogeneousLocalization.Away 𝒜 f :=
  (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).hom.hom.comp
    ((Proj.awayι 𝒜 f f_deg Nat.one_pos).appLE (Proj.basicOpen 𝒜 f) ⊤ (by
        rw [← Proj.opensRange_awayι 𝒜 f f_deg Nat.one_pos]; exact le_top |>.trans_eq
          (by simp))).hom

/-- `awayCoord` is a left inverse of `Proj.awayToSection`. -/
theorem awayCoord_awayToSection {A : Type u} [CommRing A] {σ : Type*} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (f : A) (f_deg : f ∈ 𝒜 1)
    (a : HomogeneousLocalization.Away 𝒜 f) :
    awayCoord 𝒜 f f_deg ((Proj.awayToSection 𝒜 f).hom a) = a := by
  change (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).hom.hom
    ((Proj.awayι 𝒜 f f_deg Nat.one_pos).appLE (Proj.basicOpen 𝒜 f) ⊤ (by
      rw [← Proj.opensRange_awayι 𝒜 f f_deg Nat.one_pos]; exact le_top |>.trans_eq
        (by simp)) |>.hom ((Proj.awayToSection 𝒜 f).hom a)) = a
  have h := Proj.basicOpenToSpec_app_top 𝒜 f
  unfold Proj.awayι
  rw [Scheme.Hom.comp_appLE]
  set I := Proj.basicOpenIsoSpec 𝒜 f f_deg Nat.one_pos with hI
  have hW : (Proj.basicOpen 𝒜 f).ι ⁻¹ᵁ Proj.basicOpen 𝒜 f ≤ I.hom ⁻¹ᵁ ⊤ := fun x _ => by simp
  have hW' : (⊤ : (Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).Opens) ≤ I.inv ⁻¹ᵁ ((Proj.basicOpen 𝒜 f).ι ⁻¹ᵁ Proj.basicOpen 𝒜 f) := fun x _ => by
    simp
  have hψ : ∀ y : Γ(Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f)), ⊤),
      (Scheme.Hom.appLE I.inv ((Proj.basicOpen 𝒜 f).ι ⁻¹ᵁ Proj.basicOpen 𝒜 f) ⊤ hW').hom
        ((Scheme.Hom.appLE I.hom ⊤ ((Proj.basicOpen 𝒜 f).ι ⁻¹ᵁ Proj.basicOpen 𝒜 f) hW).hom y) = y := by
    intro y
    have gen : ∀ {Z : Scheme.{u}} (g : Z ⟶ Z) (hg : g = 𝟙 Z) (e : (⊤ : Z.Opens) ≤ g ⁻¹ᵁ ⊤),
        g.appLE ⊤ ⊤ e = 𝟙 _ := by
      intro Z g hg e; subst hg; simp [Scheme.Hom.appLE]; exact Z.presheaf.map_id _
    have e2 := Scheme.Hom.comp_appLE I.inv I.hom ⊤ ⊤ (by simp)
    rw [gen _ I.inv_hom_id] at e2
    have e1 := Scheme.Hom.map_appLE I.inv hW' (homOfLE hW).op
    have e3 : Scheme.Hom.appLE I.hom ⊤ ((Proj.basicOpen 𝒜 f).ι ⁻¹ᵁ Proj.basicOpen 𝒜 f) hW ≫
        Scheme.Hom.appLE I.inv ((Proj.basicOpen 𝒜 f).ι ⁻¹ᵁ Proj.basicOpen 𝒜 f) ⊤ hW' = 𝟙 _ := by
      rw [Scheme.Hom.appLE, Category.assoc, e1]
      exact e2.symm
    exact congrArg (fun φ => φ.hom y) e3
  have hmain : (Scheme.Hom.app (Proj.basicOpen 𝒜 f).ι (Proj.basicOpen 𝒜 f)).hom
        ((Proj.awayToSection 𝒜 f).hom a) =
      (Scheme.Hom.appLE I.hom ⊤ ((Proj.basicOpen 𝒜 f).ι ⁻¹ᵁ Proj.basicOpen 𝒜 f) hW).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).inv.hom a) := by
    have h' := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).inv.hom a)) h
    simp only [] at h'
    rw [Scheme.Hom.appLE]
    change _ = ((Proj.basicOpen 𝒜 f).toScheme.presheaf.map _).hom (((Proj.basicOpenToSpec 𝒜 f).app ⊤).hom _)
    rw [h']
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).hom.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).inv.hom a) = a :=
      Iso.inv_hom_id_apply _ _
    change _ = ((Proj.basicOpen 𝒜 f).toScheme.presheaf.map _).hom
      ((Proj.basicOpen 𝒜 f).topIso.inv.hom ((Proj.awayToSection 𝒜 f).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).hom.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).inv.hom a))))
    rw [h2]
    generalize (Proj.awayToSection 𝒜 f).hom a = t
    rfl
  change (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).hom.hom
    ((Scheme.Hom.appLE I.inv ((Proj.basicOpen 𝒜 f).ι ⁻¹ᵁ Proj.basicOpen 𝒜 f) ⊤ hW').hom
      ((Scheme.Hom.app (Proj.basicOpen 𝒜 f).ι (Proj.basicOpen 𝒜 f)).hom
        ((Proj.awayToSection 𝒜 f).hom a))) = a
  rw [hmain, hψ]
  exact Iso.inv_hom_id_apply _ _

end AwayCoord

section ProjLineCharts

open Stacks.AlgebraicGeometry.ProjPolyChart

attribute [local instance] MvPolynomial.gradedAlgebra

/-- If `g` restricts on the `x`-chart to `chartMap hU e`, then on the chart `D₊(X 0)` of `Proj` the
morphism `(projectiveLineIsoProj K).inv ≫ g` is `Spec` of the composite of `e⁻¹` with
`projectiveLineProjChartRingEquiv K 0`, followed by `hU.fromSpec`. -/
theorem awayι_comp_inv_comp_eq_specMap_comp_fromSpec {K : Type u} [Field K] {C : Scheme.{u}}
    {U : C.Opens}
    (hU : IsAffineOpen U) (e : K[X] ≃+* Γ(C, U)) (g : projectiveLine K ⟶ C)
    (hg : projectiveLineXChart K ≫ g = chartMap hU e) :
    Proj.awayι (polyGrading K 1) (MvPolynomial.X 0) (X_mem_one K 1 0) Nat.one_pos ≫
      ((projectiveLineIsoProj K).inv ≫ g) =
      Spec.map (CommRingCat.ofHom ((projectiveLineProjChartRingEquiv K 0).toRingHom.comp
        e.symm.toRingHom)) ≫ hU.fromSpec := by
  have h1 : projectiveLineProjChart K 0 ≫ ((projectiveLineIsoProj K).inv ≫ g) = chartMap hU e := by
    rw [← projectiveLineXChart_comp_projectiveLineIsoProj_hom, Category.assoc,
      Iso.hom_inv_id_assoc, hg]
  have h2 : Proj.awayι (polyGrading K 1) (MvPolynomial.X 0) (X_mem_one K 1 0) Nat.one_pos =
      Spec.map (CommRingCat.ofHom (projectiveLineProjChartRingEquiv K 0).toRingHom) ≫
        projectiveLineProjChart K 0 := by
    unfold projectiveLineProjChart
    rw [← Category.assoc, ← Spec.map_comp]
    have : CommRingCat.ofHom (projectiveLineProjChartRingEquiv K 0).symm.toRingHom ≫
          CommRingCat.ofHom (projectiveLineProjChartRingEquiv K 0).toRingHom = 𝟙 _ :=
      CommRingCat.hom_ext (RingHom.ext fun a => (projectiveLineProjChartRingEquiv K 0).apply_symm_apply a)
    rw [this, Spec.map_id, Category.id_comp]
  rw [h2, Category.assoc, h1]
  unfold chartMap
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

/-- The map on sections over `U` of `Spec.map φ ≫ hU.fromSpec` is `φ`, up to `Scheme.ΓSpecIso`. -/
theorem appLE_specMap_fromSpec {C : Scheme.{u}} {U : C.Opens} (hU : IsAffineOpen U)
    {R : CommRingCat.{u}} (φ : Γ(C, U) ⟶ R) (h : (⊤ : (Spec R).Opens) ≤ (Spec.map φ ≫ hU.fromSpec) ⁻¹ᵁ U) :
    (Spec.map φ ≫ hU.fromSpec).appLE U ⊤ h ≫ (Scheme.ΓSpecIso R).hom = φ := by
  have h1 := IsAffineOpen.SpecMap_appLE_fromSpec (Spec.map φ ≫ hU.fromSpec) hU (isAffineOpen_top (Spec R)) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h1
  have h2 : Spec.map ((Spec.map φ ≫ hU.fromSpec).appLE U ⊤ h) = Spec.map (φ ≫ (Scheme.ΓSpecIso R).inv) := by
    rw [Spec.map_comp]
    exact (cancel_mono hU.fromSpec).1 (by rw [h1]; simp)
  have h3 := Spec.map_injective h2
  rw [h3]; simp

/-- `Stacks.ProjectiveChart.chartRingEquiv` sends constants to constants. -/
theorem chartRingEquiv_C' {n : ℕ} (K : Type u) [Field K] (j : Fin (n + 1)) (r : K) :
    Stacks.ProjectiveChart.chartRingEquiv K j (MvPolynomial.C r) =
      algebraMap K (Stacks.ProjectiveChart.ChartRing K n j) r := by
  have h : ∀ r : K, (Stacks.ProjectiveChart.degreeZeroEquiv K n).symm r =
      algebraMap K (Stacks.ProjectiveChart.Deg0 K n) r := fun r => by
    apply Subtype.ext
    rw [SetLike.GradeZero.coe_algebraMap, MvPolynomial.algebraMap_eq]
    rfl
  rw [Stacks.ProjectiveChart.chartRingEquiv, RingEquiv.trans_apply, MvPolynomial.mapEquiv_apply,
    MvPolynomial.map_C]
  simp only [RingEquiv.coe_toRingHom, h]
  show (Stacks.ProjectiveChart.chartHom K j) (MvPolynomial.C (algebraMap K (Stacks.ProjectiveChart.Deg0 K n) r)) = _
  exact MvPolynomial.aeval_C _ _

/-- `projectiveLineProjChartRingEquiv K 0` agrees with `Stacks.ProjectiveChart.chartRingEquiv K 0`
under `MvPolynomial.uniqueAlgEquiv`. -/
theorem chartEquiv_agree (K : Type u) [Field K] (p : K[X]) :
    projectiveLineProjChartRingEquiv K 0 p =
      Stacks.ProjectiveChart.chartRingEquiv K 0
        ((MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingEquiv.symm p) := by
  have : (projectiveLineProjChartRingEquiv K 0).toRingHom =
      (Stacks.ProjectiveChart.chartRingEquiv K 0).toRingHom.comp
        (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingEquiv.symm.toRingHom := by
    refine Polynomial.ringHom_ext (fun k => ?_) ?_
    · simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingHom.comp_apply,
        projectiveLineProjChartRingEquiv_C]
      have h : (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingEquiv.symm (Polynomial.C k) =
          MvPolynomial.C k := by simp
      rw [h, chartRingEquiv_C']
      rfl
    · simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingHom.comp_apply,
        projectiveLineProjChartRingEquiv_X]
      have hd : (default : Fin 1) = 0 := rfl
      have h0 : (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingEquiv.symm Polynomial.X
          = MvPolynomial.X (0 : Fin 1) := by simp [hd]
      have h1 : Stacks.ProjectiveChart.chartRingEquiv K (0 : Fin 2) (MvPolynomial.X (0 : Fin 1))
          = Stacks.ProjectiveChart.ratio K 0 1 := by
        rw [Stacks.ProjectiveChart.chartRingEquiv, RingEquiv.trans_apply,
          MvPolynomial.mapEquiv_apply, MvPolynomial.map_X]
        show Stacks.ProjectiveChart.chartHom K (0 : Fin 2) (MvPolynomial.X (0 : Fin 1)) = _
        rw [Stacks.ProjectiveChart.chartHom, MvPolynomial.aeval_X]
        rfl
      rw [h0, h1]
      unfold chartCoord Stacks.ProjectiveChart.ratio
      refine HomogeneousLocalization.val_injective _ ?_
      simp [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.isLocalizationElem,
        projectiveLineProjChartVar]
  exact congrArg (fun φ => φ p) this

/-- `appLE` of equal morphisms are equal. -/
theorem appLE_congr_morphism {A C : Scheme.{u}} {U : C.Opens} {V : A.Opens} {f1 f2 : A ⟶ C}
    (h : f1 = f2) (e1 : V ≤ f1 ⁻¹ᵁ U) (e2 : V ≤ f2 ⁻¹ᵁ U) : f1.appLE U V e1 = f2.appLE U V e2 := by
  subst h; rfl

/-- The map on sections of `(projectiveLineIsoProj K).inv ≫ g` from `U` to `D₊(X 0)` sends `e p` to
the section `Stacks.ProjectiveChart.sectionsChartEquiv K 0` of `p`. -/
theorem chart_sections {K : Type u} [Field K] {C : Scheme.{u}} {U : C.Opens}
    (hU : IsAffineOpen U) (e : K[X] ≃+* Γ(C, U)) (g : projectiveLine K ⟶ C)
    (hg : projectiveLineXChart K ≫ g = chartMap hU e)
    (h : Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 0) ≤
      ((projectiveLineIsoProj K).inv ≫ g) ⁻¹ᵁ U) (p : K[X]) :
    (((projectiveLineIsoProj K).inv ≫ g).appLE U
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 0)) h).hom
        (e p) =
      Stacks.ProjectiveChart.sectionsChartEquiv K 0
        ((MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingEquiv.symm p) := by
  have hdeg : (MvPolynomial.X 0 : MvPolynomial (Fin (1 + 1)) K) ∈
      MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K 1 := Stacks.ProjectiveChart.X_mem_degree_one K 0
  have hTq : awayCoord (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 0) hdeg
      ((((projectiveLineIsoProj K).inv ≫ g).appLE U
          (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 0)) h).hom (e p))
      = projectiveLineProjChartRingEquiv K 0 p := by
    have c1 := Scheme.Hom.appLE_comp_appLE
      (Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 0) hdeg Nat.one_pos)
      ((projectiveLineIsoProj K).inv ≫ g) U
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 0)) ⊤ h
      (by rw [← Proj.opensRange_awayι _ _ hdeg Nat.one_pos]; exact le_top |>.trans_eq (by simp))
    have hw : (⊤ : (Spec (CommRingCat.of (HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 0)))).Opens) ≤
      (Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 0) hdeg Nat.one_pos ≫
        (projectiveLineIsoProj K).inv ≫ g) ⁻¹ᵁ U := by
      intro x _
      apply h
      rw [← Proj.opensRange_awayι _ _ hdeg Nat.one_pos]
      exact ⟨x, rfl⟩
    have hw' : (⊤ : (Spec (CommRingCat.of (HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 0)))).Opens) ≤
      (Spec.map (CommRingCat.ofHom ((projectiveLineProjChartRingEquiv K 0).toRingHom.comp
        e.symm.toRingHom)) ≫ hU.fromSpec) ⁻¹ᵁ U := by
      rw [← awayι_comp_inv_comp_eq_specMap_comp_fromSpec hU e g hg]; exact hw
    have c2 := appLE_congr_morphism (U := U) (V := (⊤ : (Spec (CommRingCat.of (HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 0)))).Opens))
      (awayι_comp_inv_comp_eq_specMap_comp_fromSpec hU e g hg) hw hw'
    have c3 := appLE_specMap_fromSpec hU (CommRingCat.ofHom ((projectiveLineProjChartRingEquiv K 0).toRingHom.comp
        e.symm.toRingHom)) hw'
    have c4 := congrArg (fun φ => φ.hom (e p)) (c1.trans c2)
    have c5 := congrArg (fun φ => φ.hom (e p)) c3
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at c4 c5
    unfold awayCoord
    rw [RingHom.comp_apply, c4, c5]
    simp
  obtain ⟨a, ha⟩ := (Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K)
    (MvPolynomial.X 0) hdeg Nat.one_pos).commRingCatIsoToRingEquiv.surjective
    ((((projectiveLineIsoProj K).inv ≫ g).appLE U
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 0)) h).hom (e p))
  have ha' : (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 0)).hom a =
      (((projectiveLineIsoProj K).inv ≫ g).appLE U
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 0)) h).hom (e p) := ha
  rw [← ha']
  have hat : a = projectiveLineProjChartRingEquiv K 0 p := by
    rw [← hTq, ← ha', awayCoord_awayToSection]
  rw [hat, chartEquiv_agree]
  rfl

/-- Each chart `projectiveLineProjChart K i` is an open immersion. -/
instance projChart_isOpenImmersion {K : Type u} [CommRing K] (i : Fin (1 + 1)) :
    IsOpenImmersion (projectiveLineProjChart K i) := by
  unfold projectiveLineProjChart
  haveI : IsIso (CommRingCat.ofHom (projectiveLineProjChartRingEquiv K i).symm.toRingHom) :=
    inferInstanceAs (IsIso (projectiveLineProjChartRingEquiv K i).symm.toCommRingCatIso.hom)
  infer_instance

/-- If the chart `projectiveLineProjChart K i` followed by `(projectiveLineIsoProj K).inv ≫ g` is
`chartMap hU e`, then `D₊(X i)` lies in the preimage of `U`. -/
theorem chart_le {K : Type u} [Field K] {C : Scheme.{u}} {U : C.Opens}
    (hU : IsAffineOpen U) (e : K[X] ≃+* Γ(C, U)) (g : projectiveLine K ⟶ C) (i : Fin (1 + 1))
    (hg : projectiveLineProjChart K i ≫ ((projectiveLineIsoProj K).inv ≫ g) = chartMap hU e) :
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X i) ≤
      ((projectiveLineIsoProj K).inv ≫ g) ⁻¹ᵁ U := by
  have hr : (projectiveLineProjChart K i).opensRange =
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X i) := by
    unfold projectiveLineProjChart
    haveI : IsIso (CommRingCat.ofHom (projectiveLineProjChartRingEquiv K i).symm.toRingHom) :=
      inferInstanceAs (IsIso (projectiveLineProjChartRingEquiv K i).symm.toCommRingCatIso.hom)
    rw [Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι]
  intro x hx
  rw [← hr] at hx
  obtain ⟨z, rfl⟩ := hx
  have h1 : (chartMap hU e) z ∈ U := by
    have : (chartMap hU e) z ∈ (chartMap hU e).opensRange := ⟨z, rfl⟩
    rwa [chartMap_opensRange] at this
  rwa [← hg] at h1

end ProjLineCharts

end D2Lemmas

section ChartGenerators

open TopologicalSpace Stacks.PicardUFD Stacks.ProjectiveChart AlgebraicGeometry.ProjectiveSpectrum.Proj Stacks.Divisors
open Stacks.SheafOfModules Stacks.SheafOfModules.TensorStalkRingedSpace RingedSpaceModuleAdjunction

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- An invertible sheaf `L` on `Proj R[T₀, T₁]` with generators over `D₊(T₀)` and `D₊(T₁)` whose
transition on the overlap is `a · (T₁/T₀)^m`, `a` a unit over `D₊(T₀)`, is isomorphic to `𝒪(m)`. -/
theorem iso_twist_of_generators {R : Type u} [CommRing R] [IsDomain R]
    (L : (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) R)).Modules)
    (g₀ : GeneratorSections (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) R)).toRingedSpace L
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) R)
        (MvPolynomial.X (0 : Fin (1 + 1)))))
    (g₁ : GeneratorSections (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) R)).toRingedSpace L
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) R)
        (MvPolynomial.X (1 : Fin (1 + 1)))))
    (m : ℤ) (a : (Γ(AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) R),
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) R)
        (MvPolynomial.X (0 : Fin (1 + 1)))))ˣ)
    (h : generatorRatioUnit L _ (generatorRestrict L inf_le_right g₁)
        (generatorRestrict L inf_le_left g₀) =
      overlapResUnits R (0 : Fin (1 + 1)) 1 a * overlapRatioUnit R m (0 : Fin (1 + 1)) 1) :
    Nonempty (L ≅ twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) R) m) := by
  let U₀ := Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) R)
    (MvPolynomial.X (0 : Fin (1 + 1)))
  let U₁ := Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) R)
    (MvPolynomial.X (1 : Fin (1 + 1)))
  refine ⟨isoOfTransitionEqPair L
    (generatorSmulUnit L a⁻¹ g₀) g₁
    (twistChartGenerator R m (0 : Fin (1 + 1))) (twistChartGenerator R m (1 : Fin (1 + 1)))
    (le_sup_basicOpen_X R) ?_⟩
  have hsmul := generatorRatio_smul L (U₀ ⊓ U₁)
    (generatorRestrict L (inf_le_right : U₀ ⊓ U₁ ≤ U₁) g₁)
    (generatorRestrict L (inf_le_left : U₀ ⊓ U₁ ≤ U₀) g₀)
    (generatorRestrict L (inf_le_left : U₀ ⊓ U₁ ≤ U₀) (generatorSmulUnit L a⁻¹ g₀))
    (overlapResUnits R (0 : Fin (1 + 1)) 1 a)⁻¹.val
    (PresheafOfModules.map_smul L.val (homOfLE (inf_le_left : U₀ ⊓ U₁ ≤ U₀)).op a⁻¹.val
      g₀.val)
  have hcancel : ((overlapResUnits R (0 : Fin (1 + 1)) 1 a)⁻¹ *
        (overlapResUnits R (0 : Fin (1 + 1)) 1 a *
          overlapRatioUnit R m (0 : Fin (1 + 1)) 1)).val =
      (overlapRatioUnit R m (0 : Fin (1 + 1)) 1).val :=
    congrArg Units.val (inv_mul_cancel_left _ _)
  refine Eq.trans (Units.ext ?_) (generatorRatioUnit_twistChartGenerator R m 0 1).symm
  refine hsmul.trans (Eq.trans ?_ hcancel)
  exact congrArg (fun z => (overlapResUnits R (0 : Fin (1 + 1)) 1 a)⁻¹.val * z)
    ((generatorRatioUnit_val L _ _ _).symm.trans (congrArg Units.val h))

/-- Generators `s₀`, `s₁` of an invertible sheaf `L` over `U₀`, `U₁` pull back to generators over
opens `D₀`, `D₁` above them, whose transition unit is the image under `f.appLE` of that of `s₀`,
`s₁`. -/
theorem exists_pullback_generators {P C : Scheme.{u}} (f : P ⟶ C) (L : C.Modules)
    (hL : IsInvertible C.presheaf (structureSheafRing C.toRingedSpace).property L)
    (U₀ U₁ : C.Opens) (s₀ : GeneratorSections C.toRingedSpace L U₀)
    (s₁ : GeneratorSections C.toRingedSpace L U₁) (D₀ D₁ : P.Opens)
    (h₀ : D₀ ≤ f ⁻¹ᵁ U₀) (h₁ : D₁ ≤ f ⁻¹ᵁ U₁) :
    ∃ (G₀ : GeneratorSections P.toRingedSpace ((modulePullback f.toLRSHom.toShHom).obj L) D₀)
      (G₁ : GeneratorSections P.toRingedSpace ((modulePullback f.toLRSHom.toShHom).obj L) D₁),
      generatorRatioUnit ((modulePullback f.toLRSHom.toShHom).obj L) (D₀ ⊓ D₁)
        (generatorRestrict _ inf_le_right G₁) (generatorRestrict _ inf_le_left G₀) =
      Units.map (f.appLE (U₀ ⊓ U₁) (D₀ ⊓ D₁)
        (le_inf (inf_le_left.trans h₀) (inf_le_right.trans h₁))).hom.toMonoidHom
        (generatorRatioUnit L (U₀ ⊓ U₁) (generatorRestrict L inf_le_right s₁)
          (generatorRestrict L inf_le_left s₀)) := by
  have hW : D₀ ⊓ D₁ ≤ f ⁻¹ᵁ (U₀ ⊓ U₁) :=
    le_inf (inf_le_left.trans h₀) (inf_le_right.trans h₁)
  refine ⟨generatorRestrict _ h₀ (pullbackGenerator f L hL U₀ s₀),
    generatorRestrict _ h₁ (pullbackGenerator f L hL U₁ s₁), ?_⟩
  have e0 : generatorRestrict ((modulePullback f.toLRSHom.toShHom).obj L)
      (inf_le_left : D₀ ⊓ D₁ ≤ D₀)
      (generatorRestrict _ h₀ (pullbackGenerator f L hL U₀ s₀)) =
      generatorRestrict _ hW (pullbackGenerator f L hL (U₀ ⊓ U₁)
        (generatorRestrict L inf_le_left s₀)) := by
    rw [← pullbackGenerator_restrict f L hL (inf_le_left : U₀ ⊓ U₁ ≤ U₀) s₀]
    exact (generatorRestrict_trans _ _ _ _).trans (generatorRestrict_trans _ _ _ _).symm
  have e1 : generatorRestrict ((modulePullback f.toLRSHom.toShHom).obj L)
      (inf_le_right : D₀ ⊓ D₁ ≤ D₁)
      (generatorRestrict _ h₁ (pullbackGenerator f L hL U₁ s₁)) =
      generatorRestrict _ hW (pullbackGenerator f L hL (U₀ ⊓ U₁)
        (generatorRestrict L inf_le_right s₁)) := by
    rw [← pullbackGenerator_restrict f L hL (inf_le_right : U₀ ⊓ U₁ ≤ U₁) s₁]
    exact (generatorRestrict_trans _ _ _ _).trans (generatorRestrict_trans _ _ _ _).symm
  rw [e0, e1]
  refine (generatorRatioUnit_restrict _ hW _ _).trans ?_
  rw [generatorRatioUnit_pullbackGenerator]
  ext1
  rfl

/-- If `g • G = g' • G'` for generators `G`, `G'` over `W`, then
`g = g' * generatorRatio L W G G'`. -/
theorem mul_ratio_eq {X : RingedSpace.{u, u}}
    (L : _root_.SheafOfModules.{u} (structureSheaf X.sheaf)) (W : Opens X.carrier)
    (G G' : GeneratorSections X L W)
    (g g' : (structureSheaf X.sheaf).obj.obj (op W))
    (h : g • G.val = g' • G'.val) : g = g' * generatorRatio L W G G' := by
  have hρ := generatorRatio_spec L W G G'
  have h1 : g • G.val = (g' * generatorRatio L W G G') • G.val := by
    rw [h, hρ, mul_smul]
  exact (G.property W le_rfl).injective (by simpa only [generator_restrict_self] using h1)

/-- `f.appLE` commutes with restriction maps. -/
theorem res_comm {A C : Scheme.{u}} (f : A ⟶ C) {U W : C.Opens} {D D' : A.Opens}
    (hDU : D ≤ f ⁻¹ᵁ U) (hD'W : D' ≤ f ⁻¹ᵁ W) (hWU : W ≤ U) (hD : D' ≤ D) (x : Γ(C, U)) :
    (f.appLE W D' hD'W).hom (C.presheaf.map (homOfLE hWU).op x) =
      A.presheaf.map (homOfLE hD).op ((f.appLE U D hDU).hom x) := by
  have e1 := Scheme.Hom.map_appLE f (U := W) (V := D') (U' := U) hD'W (homOfLE hWU).op
  have e2 := Scheme.Hom.appLE_map f hDU (homOfLE hD).op
  exact (congrArg (fun φ => φ.hom x) e1).trans (congrArg (fun φ => φ.hom x) e2).symm

/-- The kernel of `inclSections h U` is the kernel of the map on sections over `I.subschemeι ⁻¹ᵁ U`
of `Scheme.IdealSheafData.inclusion h`. -/
theorem ker_inclSections_eq_ker_app {Y : Scheme.{u}} {I Ej : Y.IdealSheafData} (h : I ≤ Ej)
    (U : Y.Opens) :
    RingHom.ker (inclSections h U) =
      RingHom.ker ((Scheme.IdealSheafData.inclusion h).app (I.subschemeι ⁻¹ᵁ U)).hom := by
  have hpre : (Scheme.IdealSheafData.inclusion h) ⁻¹ᵁ (I.subschemeι ⁻¹ᵁ U) =
      Ej.subschemeι ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, Scheme.IdealSheafData.inclusion_subschemeι]
  have key : ∀ (V : Ej.subscheme.Opens)
      (hV : (Scheme.IdealSheafData.inclusion h) ⁻¹ᵁ (I.subschemeι ⁻¹ᵁ U) = V)
      (e : V ≤ (Scheme.IdealSheafData.inclusion h) ⁻¹ᵁ (I.subschemeι ⁻¹ᵁ U)),
      RingHom.ker ((Scheme.IdealSheafData.inclusion h).appLE (I.subschemeι ⁻¹ᵁ U) V e).hom =
        RingHom.ker ((Scheme.IdealSheafData.inclusion h).app (I.subschemeι ⁻¹ᵁ U)).hom := by
    intro V hV e
    subst hV
    rw [Scheme.Hom.appLE_eq_app]
  exact key _ hpre _

/-- Let `D` be an effective Cartier divisor and `I₂ ≤ I₁ ≤ D`. If `y` generates the kernel of the
restriction of sections over `U` from `I₂` to `D`, the annihilator of `y` maps to zero in `I₁`,
and the kernel of the restriction from `I₂` to `I₁` is nil, then the pullback of `𝒪(D)` has a
generator `G` over `U` with the canonical section restricting to `y • G`. -/
theorem exists_coeff_generator {Y : Scheme.{u}} (D : Y.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D]
    {I₁ I₂ : Y.IdealSheafData} (h₂₁ : I₂ ≤ I₁) (h₁D : I₁ ≤ D) (U : Y.Opens)
    (hU : IsAffineOpen (I₂.subschemeι ⁻¹ᵁ U))
    (G0 : GeneratorSections I₂.subscheme.toRingedSpace
      ((Scheme.Modules.pullback I₂.subschemeι).obj (Stacks.Divisors.modulesInvertibleSheaf D))
      (I₂.subschemeι ⁻¹ᵁ U))
    (y : Γ(I₂.subscheme, I₂.subschemeι ⁻¹ᵁ U))
    (hker : RingHom.ker (inclSections (h₂₁.trans h₁D) U) = Ideal.span {y})
    (hann : ∀ z, z * y = 0 → inclSections h₂₁ U z = 0)
    (hnil : ∀ n ∈ RingHom.ker (inclSections h₂₁ U), IsNilpotent n) :
    ∃ G : GeneratorSections I₂.subscheme.toRingedSpace
      ((Scheme.Modules.pullback I₂.subschemeι).obj (Stacks.Divisors.modulesInvertibleSheaf D))
      (I₂.subschemeι ⁻¹ᵁ U),
      ((Scheme.Modules.pullback I₂.subschemeι).obj
          (Stacks.Divisors.modulesInvertibleSheaf D)).presheaf.map (homOfLE le_top).op
        (pullbackGlobalSections I₂.subschemeι (Stacks.Divisors.modulesInvertibleSheaf D)
          (Stacks.Divisors.canonicalSection D)) =
        y • (show Γ((Scheme.Modules.pullback I₂.subschemeι).obj
          (Stacks.Divisors.modulesInvertibleSheaf D), I₂.subschemeι ⁻¹ᵁ U) from G.val) := by
  have hbij : Function.Bijective (fun r : Γ(I₂.subscheme, I₂.subschemeι ⁻¹ᵁ U) =>
      r • (show Γ((Scheme.Modules.pullback I₂.subschemeι).obj
          (Stacks.Divisors.modulesInvertibleSheaf D), I₂.subschemeι ⁻¹ᵁ U) from G0.val)) := by
    have h0 := generator_restrict_self (X := I₂.subscheme.toRingedSpace)
      ((Scheme.Modules.pullback I₂.subschemeι).obj (Stacks.Divisors.modulesInvertibleSheaf D))
      (I₂.subschemeι ⁻¹ᵁ U) G0
    have := G0.property (I₂.subschemeι ⁻¹ᵁ U) le_rfl
    rw [h0] at this
    exact this
  let M := (Scheme.Modules.pullback I₂.subschemeι).obj (Stacks.Divisors.modulesInvertibleSheaf D)
  let U' := I₂.subschemeι ⁻¹ᵁ U
  let χ₁ : Γ(M, U') := M.presheaf.map (homOfLE (le_top : U' ≤ ⊤)).op
    (pullbackGlobalSections I₂.subschemeι (Stacks.Divisors.modulesInvertibleSheaf D)
      (Stacks.Divisors.canonicalSection D))
  obtain ⟨a, ha⟩ := hbij.2 χ₁
  let e : Γ(M, U') ≃ₗ[Γ(I₂.subscheme, U')] Γ(I₂.subscheme, U') :=
    (LinearEquiv.ofBijective (LinearMap.toSpanSingleton Γ(I₂.subscheme, U') Γ(M, U')
      (show Γ(M, U') from G0.val)) (show Function.Bijective (LinearMap.toSpanSingleton Γ(I₂.subscheme, U') Γ(M, U')
        (show Γ(M, U') from G0.val)) from hbij)).symm
  have he : e χ₁ = a := by
    rw [LinearEquiv.symm_apply_eq]
    exact ha.symm
  have hk := ker_inclusion_app_eq_span D I₂ (h₂₁.trans h₁D) ⟨U', hU⟩ e a he
  rw [← ker_inclSections_eq_ker_app, hker] at hk
  obtain ⟨β, hβ⟩ := Ideal.mem_span_singleton'.1 (hk ▸ Ideal.mem_span_singleton_self y)
  obtain ⟨α, hα⟩ := Ideal.mem_span_singleton'.1 (hk.symm ▸ Ideal.mem_span_singleton_self a)
  have h1 : (1 - β * α) * y = 0 := by
    rw [sub_mul, one_mul, mul_assoc, hα, hβ, sub_self]
  have hmem : (1 - β * α) ∈ RingHom.ker (inclSections h₂₁ U) := hann _ h1
  have hunit : IsUnit (β * α) := by simpa using (hnil _ hmem).isUnit_one_sub
  have hαu : IsUnit α := isUnit_of_mul_isUnit_right hunit
  refine ⟨generatorSmulUnit _ hαu.unit G0, ?_⟩
  have h2 : y • ((α : Γ(I₂.subscheme, U')) • (show Γ(M, U') from G0.val)) =
      a • (show Γ(M, U') from G0.val) := by
    rw [← hα, ← mul_smul, mul_comm]
  exact ha.symm.trans h2.symm

/-- Let `g` identify the projective line with `Ej.subscheme`, with charts `e₀`, `e₁`. If generators
`Ca`, `Cb` of an invertible sheaf `L'` over `V₀`, `V₁` have transition unit `c · uEⁿ`, where
`c ≠ 0` and `uE` is the restriction of `e₀ X`, then the pullback of `L'` to `Proj` is
isomorphic to `𝒪(-n)`. -/
theorem final_iso_core2 {K : Type u} [Field K] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of K))
    (Ej : Y.IdealSheafData) (L' : Ej.subscheme.Modules)
    (hL' : IsInvertible Ej.subscheme.presheaf (structureSheafRing Ej.subscheme.toRingedSpace).property L')
    (V0 V1 : Y.Opens)
    (Ca : GeneratorSections Ej.subscheme.toRingedSpace L' (Ej.subschemeι ⁻¹ᵁ V0))
    (Cb : GeneratorSections Ej.subscheme.toRingedSpace L' (Ej.subschemeι ⁻¹ᵁ V1))
    (g : projectiveLine K ⟶ Ej.subscheme)
    (hU0 : IsAffineOpen (Ej.subschemeι ⁻¹ᵁ V0)) (hU1 : IsAffineOpen (Ej.subschemeι ⁻¹ᵁ V1))
    (e0 : Polynomial K ≃+* Γ(Ej.subscheme, Ej.subschemeι ⁻¹ᵁ V0))
    (e1 : Polynomial K ≃+* Γ(Ej.subscheme, Ej.subschemeι ⁻¹ᵁ V1))
    (hg0c : projectiveLineXChart K ≫ g = chartMap hU0 e0)
    (hg1c : projectiveLineYChart K ≫ g = chartMap hU1 e1)
    (c : K) (hc : c ≠ 0) (n : ℤ)
    (uE : (Γ(Ej.subscheme, Ej.subschemeι ⁻¹ᵁ (V0 ⊓ V1)))ˣ)
    (huE : (uE : Γ(Ej.subscheme, Ej.subschemeι ⁻¹ᵁ (V0 ⊓ V1))) =
      (Ej.subscheme.presheaf.map (homOfLE (Scheme.Hom.preimage_mono Ej.subschemeι
        (inf_le_left : V0 ⊓ V1 ≤ V0))).op).hom (e0 Polynomial.X))
    (hrel : ((generatorRatioUnit L' (Ej.subschemeι ⁻¹ᵁ V0 ⊓ Ej.subschemeι ⁻¹ᵁ V1)
        (generatorRestrict L' inf_le_right Cb) (generatorRestrict L' inf_le_left Ca)).val :
          Γ(Ej.subscheme, Ej.subschemeι ⁻¹ᵁ V0 ⊓ Ej.subschemeι ⁻¹ᵁ V1)) =
        sigmaSub sY Ej (V0 ⊓ V1) c * ((uE ^ n : (Γ(Ej.subscheme, Ej.subschemeι ⁻¹ᵁ (V0 ⊓ V1)))ˣ) :
          Γ(Ej.subscheme, Ej.subschemeι ⁻¹ᵁ (V0 ⊓ V1)))) :
    Nonempty ((Scheme.Modules.pullback ((projectiveLineIsoProj K).inv ≫ g)).obj L' ≅
      ProjectiveSpectrum.Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin 2) K) (-n)) := by
  have hD0 := chart_le hU0 e0 g 0 (by rw [← projectiveLineXChart_comp_projectiveLineIsoProj_hom, Category.assoc, Iso.hom_inv_id_assoc, hg0c])
  have hD1 := chart_le hU1 e1 g 1 (by rw [← projectiveLineYChart_comp_projectiveLineIsoProj_hom, Category.assoc, Iso.hom_inv_id_assoc, hg1c])
  obtain ⟨G₀, G₁, hG⟩ := exists_pullback_generators ((projectiveLineIsoProj K).inv ≫ g) L' hL'
    (Ej.subschemeι ⁻¹ᵁ V0) (Ej.subschemeι ⁻¹ᵁ V1) Ca Cb
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 0))
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 1))
    hD0 hD1
  have hu : IsUnit (sigmaSub sY Ej V0 c) := (isUnit_iff_ne_zero.2 hc).map _
  have hWle : Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 0) ⊓
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 1) ≤
      ((projectiveLineIsoProj K).inv ≫ g) ⁻¹ᵁ (Ej.subschemeι ⁻¹ᵁ (V0 ⊓ V1)) :=
    le_inf (inf_le_left.trans hD0) (inf_le_right.trans hD1)
  have hWU : Ej.subschemeι ⁻¹ᵁ (V0 ⊓ V1) ≤ Ej.subschemeι ⁻¹ᵁ V0 :=
    Scheme.Hom.preimage_mono _ inf_le_left
  have key : ∀ x : Γ(Ej.subscheme, Ej.subschemeι ⁻¹ᵁ V0),
      (((projectiveLineIsoProj K).inv ≫ g).appLE (Ej.subschemeι ⁻¹ᵁ (V0 ⊓ V1))
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 0) ⊓
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 1)) hWle).hom
        ((Ej.subscheme.presheaf.map (homOfLE hWU).op).hom x) =
      (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K)).presheaf.map
        (homOfLE (inf_le_left : Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 0) ⊓
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 1) ≤ _)).op
        ((((projectiveLineIsoProj K).inv ≫ g).appLE (Ej.subschemeι ⁻¹ᵁ V0) _ hD0).hom x) :=
    fun x => res_comm _ hD0 hWle hWU inf_le_left x
  have e1 : (((projectiveLineIsoProj K).inv ≫ g).appLE (Ej.subschemeι ⁻¹ᵁ (V0 ⊓ V1))
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 0) ⊓
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 1)) hWle).hom
        (sigmaSub sY Ej (V0 ⊓ V1) c) =
      (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K)).presheaf.map
        (homOfLE (inf_le_left : Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 0) ⊓
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 1) ≤ _)).op
        ((((projectiveLineIsoProj K).inv ≫ g).appLE (Ej.subschemeι ⁻¹ᵁ V0) _ hD0).hom
          (sigmaSub sY Ej V0 c)) := by
    rw [← sigmaSub_restrict sY Ej (inf_le_left : V0 ⊓ V1 ≤ V0) c]
    exact key _
  have e2 : (((projectiveLineIsoProj K).inv ≫ g).appLE (Ej.subschemeι ⁻¹ᵁ (V0 ⊓ V1))
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 0) ⊓
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 1)) hWle).hom
        (uE : Γ(Ej.subscheme, Ej.subschemeι ⁻¹ᵁ (V0 ⊓ V1))) =
      ((overlapRatioUnit K (-1) 0 1 : (Γ(AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K), _))ˣ) : Γ(AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K), _)) := by
    rw [huE, key, chart_sections hU0 e0 g hg0c hD0]
    have h0 : (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingEquiv.symm Polynomial.X
        = MvPolynomial.X (0 : Fin 1) := by simp [show (default : Fin 1) = 0 from rfl]
    rw [h0]
    refine Subtype.ext (funext fun x => ?_)
    exact sectionsChartEquiv_X_apply K 0 (0 : Fin 1) inf_le_left inf_le_right x
  refine (iso_twist_of_generators (R := K) _ G₀ G₁ (-n)
    (Units.map (((projectiveLineIsoProj K).inv ≫ g).appLE (Ej.subschemeι ⁻¹ᵁ V0)
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 0)) hD0).hom.toMonoidHom
      hu.unit) (hG.trans ?_))
  refine Units.ext ?_
  have e3 : Units.map (((projectiveLineIsoProj K).inv ≫ g).appLE (Ej.subschemeι ⁻¹ᵁ (V0 ⊓ V1))
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 0) ⊓
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 1)) hWle).hom.toMonoidHom
      uE = overlapRatioUnit K (-1) 0 1 := Units.ext e2
  have e4 : Units.map (((projectiveLineIsoProj K).inv ≫ g).appLE (Ej.subschemeι ⁻¹ᵁ (V0 ⊓ V1))
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 0) ⊓
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 1)) hWle).hom.toMonoidHom
      (uE ^ n) = overlapRatioUnit K (-n) 0 1 := by
    rw [map_zpow, e3, overlapRatioUnit_zpow (R := K) (-1), overlapRatioUnit_zpow (R := K) (-n),
      ← zpow_mul]
    congr 1
    ring
  have e5 := congrArg Units.val e4
  refine (congrArg (fun z => (((projectiveLineIsoProj K).inv ≫ g).appLE (Ej.subschemeι ⁻¹ᵁ (V0 ⊓ V1))
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 0) ⊓
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 1)) hWle).hom z) hrel).trans ?_
  rw [map_mul, e1]
  exact congrArg (fun z => _ * z) e5

/-- If a global section `χ` restricts over `U` to `y • G`, then over `U' ≤ U` it restricts to the
restriction of `y` times the restriction of `G`. -/
theorem coef_restrict {Z : Scheme.{u}} (M : Z.Modules) {U U' : Z.Opens} (h : U' ≤ U)
    (χ : Γ(M, ⊤)) (y : Γ(Z, U)) (G : GeneratorSections Z.toRingedSpace M U)
    (hG : M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op χ = y • (show Γ(M, U) from G.val)) :
    M.presheaf.map (homOfLE (le_top : U' ≤ ⊤)).op χ =
      Z.presheaf.map (homOfLE h).op y • (show Γ(M, U') from (generatorRestrict M h G).val) := by
  have e1 : M.presheaf.map (homOfLE (le_top : U' ≤ ⊤)).op χ =
      M.presheaf.map (homOfLE h).op (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op χ) := by
    rw [← CategoryTheory.ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
    rfl
  rw [e1, hG]
  exact PresheafOfModules.map_smul M.val (homOfLE h).op y G.val

/-- For `j : Fin r`, the ideal attached to `j.castSucc` is `(X 1)` or `(X 0 * X 1)`. -/
theorem J_castSucc_cases {K : Type u} [Field K] {r : ℕ} (j : Fin r) :
    (if (j.castSucc : Fin (r + 1)) = 0 then Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 2) K)}
      else if (j.castSucc : Fin (r + 1)) = Fin.last r then Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) K)}
      else Ideal.span {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) K)}) =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 2) K)} ∨
    (if (j.castSucc : Fin (r + 1)) = 0 then Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 2) K)}
      else if (j.castSucc : Fin (r + 1)) = Fin.last r then Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) K)}
      else Ideal.span {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) K)}) =
      Ideal.span {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) K)} := by
  split_ifs with h1 h2
  · exact Or.inl rfl
  · exact absurd h2 (Fin.castSucc_lt_last j).ne
  · exact Or.inr rfl

/-- For `j : Fin r`, the ideal attached to `j.succ` is `(X 0)` or `(X 1 * X 0)`. -/
theorem J_succ_cases {K : Type u} [Field K] {r : ℕ} (j : Fin r) :
    (if (j.succ : Fin (r + 1)) = 0 then Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 2) K)}
      else if (j.succ : Fin (r + 1)) = Fin.last r then Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) K)}
      else Ideal.span {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) K)}) =
      Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) K)} ∨
    (if (j.succ : Fin (r + 1)) = 0 then Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 2) K)}
      else if (j.succ : Fin (r + 1)) = Fin.last r then Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) K)}
      else Ideal.span {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) K)}) =
      Ideal.span {(MvPolynomial.X 1 * MvPolynomial.X 0 : MvPolynomial (Fin 2) K)} := by
  split_ifs with h1 h2
  · exact absurd h1 (Fin.succ_ne_zero j)
  · exact Or.inl rfl
  · exact Or.inr (by rw [mul_comm])

end ChartGenerators

end

end MMP.Resolution.MarkedChain
