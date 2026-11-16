module

public import MMP.AlgebraicGeometry.Intersection.CurveClassesFiniteDim
import MMP.AlgebraicGeometry.Intersection.PairingSeparation

/-!
# Cartier coordinates on `N₁(X)` and the lattice of integral curve classes

Let `k` be an algebraically closed field of characteristic zero and `X` a proper variety over
`k`, and put `W = N₁(X)` (`MMP.Mori.NumericalCurveClasses`) with its numerical topology. Each
Cartier divisor `E` gives the evaluation `z ↦ (z · E)`, a linear form on `W`. Then `W` is finite
dimensional, the Cartier evaluations span `W^*`, and every linearly independent set of them extends
to a set whose evaluations form a basis of `W^*`. For Cartier divisors `D₁, …, D_r` whose
evaluations form a basis of `W^*`, the coordinate map `Φ = (D₁, …, D_r) : W → ℝ^r` is a linear
homeomorphism. The subgroup `Λ = Φ⁻¹(ℤ^r)` is closed and discrete, `Φ` restricts to an
isomorphism `Λ ≃ ℤ^r`, and `Λ` contains the class of every integral 1-cycle. In particular the
set of classes of integral 1-cycles is countable.

## Main results

* `MMP.Mori.NumericalCurveClasses.exists_cartier_coordinates_of_isProperVariety`: the
  statement above.

## Implementation notes

An independent family of evaluations is a set `s` of Cartier divisors on which the evaluation is
`LinearIndepOn`, and its extension is a set `t ⊇ s` on which the evaluation is independent and
spans `W^*`. A basis `D₁, …, D_r` is a family `D : ι → X.CartierDivisor` whose evaluations are
linearly independent and span `W^*`. Finiteness of `ι` follows from these and is not assumed. The
lattice `Λ` is the preimage of the integer points under `Φ`, as an additive subgroup of `W`.
Integral 1-cycles are `MMP.Mori.OneCycle ℤ sX`, sent to real cycles by coefficientwise cast.

## References

* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, Chapter 1.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Topology

namespace MMP.Mori

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}

/-- The Cartier evaluation `z ↦ (z · E)` on `N₁(X)`. -/
private noncomputable abbrev ev (sX : X ⟶ Spec (.of k)) (E : X.CartierDivisor) :
    Module.Dual ℝ (NumericalCurveClasses sX) :=
  NumericalCurveClasses.intersectionNumber (sX := sX) (KCartierDivisor.ofCartier ℝ E)

/-- On an integral scheme, a class on which every Cartier evaluation vanishes is zero. -/
private lemma eq_zero_of_forall_ev [IsIntegral X] (z : NumericalCurveClasses sX)
    (hz : ∀ E : X.CartierDivisor, ev sX E z = 0) : z = 0 := by
  obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
  refine (Submodule.Quotient.mk_eq_zero _).mpr (OneCycle.mem_numericallyTrivial.mpr fun L _ => ?_)
  obtain ⟨E, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf L
  have h0 := hz E
  rw [ev, NumericalCurveClasses.intersectionNumber_numericalClass,
    OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree] at h0
  rw [← h0, OneCycle.degree, OneCycle.degree]
  congr 2
  funext C
  exact congrArg _ (degreeOn_eq_of_iso k sX C.ι C.dim_le e)

/-- The class of an integral 1-cycle has integral Cartier evaluations. -/
private lemma ev_numericalClass_mapRange (E : X.CartierDivisor) (Z : OneCycle ℤ sX) :
    ev sX E (OneCycle.numericalClass sX (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero Z)) =
      ((OneCycle.degree ℤ sX (MMP.CartierDivisor.sheaf E) Z : ℤ) : ℝ) := by
  rw [ev, NumericalCurveClasses.intersectionNumber_numericalClass,
    OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_apply,
    OneCycle.degree_apply, Finsupp.sum_mapRange_index (by simp)]
  simp [Finsupp.sum]

section Proper

variable [IsAlgClosed k] [CharZero k] [MMP.Mori.IsVariety k sX]

/-- The Cartier evaluations span the dual of `N₁(X)`. -/
private lemma span_range_ev : Submodule.span ℝ (Set.range (ev sX)) = ⊤ := by
  haveI := finiteDimensional_numericalCurveClasses (k := k) sX
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℝ (Set.range (ev sX)))]
  have : (Submodule.span ℝ (Set.range (ev sX))).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Submodule.mem_dualCoannihilator] at hz
    exact (Submodule.mem_bot ℝ).mpr
      (eq_zero_of_forall_ev z fun E => hz _ (Submodule.subset_span ⟨E, rfl⟩))
  rw [this, Submodule.dualAnnihilator_bot]

/-- A family of Cartier divisors whose evaluations form a basis of `N₁(X)^*` is finite, and its
coordinate map `N₁(X) → ℝ^ι` is a linear homeomorphism. -/
private lemma finite_and_exists_coordinateEquiv {ι : Type*} (D : ι → X.CartierDivisor)
    (hli : LinearIndependent ℝ fun i => ev sX (D i))
    (hspan : Submodule.span ℝ (Set.range fun i => ev sX (D i)) = ⊤) :
    Finite ι ∧ ∃ Φ : NumericalCurveClasses sX ≃L[ℝ] (ι → ℝ),
      (Φ : NumericalCurveClasses sX →ₗ[ℝ] ι → ℝ) = LinearMap.pi fun i => ev sX (D i) := by
  haveI := finiteDimensional_numericalCurveClasses (k := k) sX
  let B := Module.Basis.mk hli hspan.ge
  haveI hfin : Finite ι := Module.Finite.finite_basis B
  letI := Fintype.ofFinite ι
  refine ⟨hfin, ?_⟩
  set Φ : NumericalCurveClasses sX →ₗ[ℝ] ι → ℝ := LinearMap.pi fun i => ev sX (D i)
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro z hz
    have hle : Submodule.span ℝ (Set.range fun i => ev sX (D i)) ≤
        LinearMap.ker (Module.Dual.eval ℝ _ z) :=
      Submodule.span_le.mpr <| Set.range_subset_iff.mpr fun i =>
        congrFun (LinearMap.mem_ker.mp hz) i
    rw [hspan] at hle
    exact (Submodule.mem_bot ℝ).mpr
      (eq_zero_of_forall_ev z fun E => hle (Submodule.mem_top (x := ev sX E)))
  have hrank : Module.finrank ℝ (NumericalCurveClasses sX) = Module.finrank ℝ (ι → ℝ) := by
    rw [← Subspace.dual_finrank_eq, Module.finrank_eq_card_basis B,
      Module.finrank_fintype_fun_eq_card]
  let e := LinearEquiv.ofBijective Φ
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj⟩
  have hcont : Continuous e := by
    refine continuous_pi fun i => ?_
    change Continuous (ev sX (D i))
    rw [ev, NumericalCurveClasses.intersectionNumber_ofCartier]
    exact NumericalCurveClasses.continuous_degree sX _
  have hcont' : Continuous e.symm := by
    refine continuous_iInf_rng.2 fun L => continuous_iInf_rng.2 fun h => ?_
    refine continuous_induced_rng.2 ?_
    haveI := h
    exact ((NumericalCurveClasses.degree sX L).comp
      (e.symm : (ι → ℝ) →ₗ[ℝ] NumericalCurveClasses sX)).continuous_of_finiteDimensional
  exact ⟨⟨e, hcont, hcont'⟩, rfl⟩

/-- For a continuous linear equivalence `Φ : W ≃L[ℝ] ℝ^ι` with `ι` finite, the lattice
`Φ⁻¹(ℤ^ι)` is closed and discrete, and `Φ` restricts to an isomorphism of it onto `ℤ^ι`. -/
private lemma isClosed_and_discreteTopology_comap_range_intCast {W : Type*} [AddCommGroup W]
    [Module ℝ W] [TopologicalSpace W] {ι : Type*} [Finite ι] (Φ : W ≃L[ℝ] (ι → ℝ))
    {φ : W →ₗ[ℝ] ι → ℝ} (hφ : (Φ : W →ₗ[ℝ] ι → ℝ) = φ) :
    IsClosed ((AddSubgroup.comap φ.toAddMonoidHom
        (AddMonoidHom.compLeft (Int.castAddHom ℝ) ι).range : Set W)) ∧
    DiscreteTopology (AddSubgroup.comap φ.toAddMonoidHom
        (AddMonoidHom.compLeft (Int.castAddHom ℝ) ι).range) ∧
    ∃ e : AddSubgroup.comap φ.toAddMonoidHom
        (AddMonoidHom.compLeft (Int.castAddHom ℝ) ι).range ≃+ (ι → ℤ),
      ∀ z i, ((e z i : ℤ) : ℝ) = φ z i := by
  subst hφ
  set ψ := AddMonoidHom.compLeft (Int.castAddHom ℝ) ι
  have hψ : Function.Injective ψ := fun a b h =>
    funext fun i => Int.cast_injective (congrFun h i : ((a i : ℤ) : ℝ) = b i)
  set Λ := AddSubgroup.comap (Φ : W →ₗ[ℝ] ι → ℝ).toAddMonoidHom ψ.range
  let ψ' : (ι → ℤ) →+ W := (Φ.symm : (ι → ℝ) →ₗ[ℝ] W).toAddMonoidHom.comp ψ
  have hψ' : Function.Injective ψ' := Φ.symm.injective.comp hψ
  have hrange : ψ'.range = Λ := by
    ext z
    simp only [AddMonoidHom.mem_range, AddSubgroup.mem_comap, Λ, ψ']
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, by simp⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, by simp [hn]⟩
  let e : Λ ≃+ (ι → ℤ) :=
    ((AddMonoidHom.ofInjective hψ').trans (AddEquiv.addSubgroupCongr hrange)).symm
  have he : ∀ z : Λ, ψ (e z) = Φ z := by
    intro z
    have : ψ' (e z) = z := by
      rw [← AddMonoidHom.ofInjective_apply hψ' (x := e z)]
      simp [e]
    rw [← this]
    simp [ψ']
  have hemb : IsEmbedding (fun n : ι → ℤ => fun i => (n i : ℝ)) :=
    IsEmbedding.piMap fun _ => Int.isClosedEmbedding_coe_real.isEmbedding
  have hecont : Continuous e := by
    rw [hemb.continuous_iff,
      show ((fun n : ι → ℤ => fun i => (n i : ℝ)) ∘ e) = fun z : Λ => Φ z from funext he]
    fun_prop
  refine ⟨?_, DiscreteTopology.of_continuous_injective hecont e.injective, e,
    fun z i => congrFun (he z) i⟩
  have : (Λ : Set W) = Φ ⁻¹' Set.range (fun n : ι → ℤ => fun i => (n i : ℝ)) := by
    ext z
    simp [Λ, ψ, funext_iff]
  rw [this]
  exact (IsClosedEmbedding.piMap fun _ => Int.isClosedEmbedding_coe_real).isClosed_range.preimage
    Φ.continuous

/-- For a basis `D` of Cartier evaluations, `ι` is finite, the coordinate map is a linear
homeomorphism, and `Φ⁻¹(ℤ^ι)` is a closed discrete subgroup isomorphic to `ℤ^ι` that contains
every integral 1-cycle class. -/
private lemma finite_and_exists_coordinateEquiv_and_lattice {ι : Type*} (D : ι → X.CartierDivisor)
    (hli : LinearIndependent ℝ fun i => ev sX (D i))
    (hspan : Submodule.span ℝ (Set.range fun i => ev sX (D i)) = ⊤) :
    Finite ι ∧
    (∃ Φ : NumericalCurveClasses sX ≃L[ℝ] (ι → ℝ),
      (Φ : NumericalCurveClasses sX →ₗ[ℝ] ι → ℝ) = LinearMap.pi fun i => ev sX (D i)) ∧
    IsClosed ((AddSubgroup.comap (LinearMap.pi fun i => ev sX (D i)).toAddMonoidHom
        (AddMonoidHom.compLeft (Int.castAddHom ℝ) ι).range : Set (NumericalCurveClasses sX))) ∧
    DiscreteTopology (AddSubgroup.comap (LinearMap.pi fun i => ev sX (D i)).toAddMonoidHom
        (AddMonoidHom.compLeft (Int.castAddHom ℝ) ι).range) ∧
    (∃ e : AddSubgroup.comap (LinearMap.pi fun i => ev sX (D i)).toAddMonoidHom
        (AddMonoidHom.compLeft (Int.castAddHom ℝ) ι).range ≃+ (ι → ℤ),
      ∀ z i, ((e z i : ℤ) : ℝ) = ev sX (D i) (z : NumericalCurveClasses sX)) ∧
    ∀ Z : OneCycle ℤ sX,
      OneCycle.numericalClass sX (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero Z) ∈
        AddSubgroup.comap (LinearMap.pi fun i => ev sX (D i)).toAddMonoidHom
          (AddMonoidHom.compLeft (Int.castAddHom ℝ) ι).range := by
  obtain ⟨hfin, Φ, hΦ⟩ := finite_and_exists_coordinateEquiv D hli hspan
  obtain ⟨h1, h2, e, he⟩ := isClosed_and_discreteTopology_comap_range_intCast Φ hΦ
  exact ⟨hfin, ⟨Φ, hΦ⟩, h1, h2, ⟨e, he⟩, fun Z =>
    ⟨fun i => OneCycle.degree ℤ sX (MMP.CartierDivisor.sheaf (D i)) Z,
      funext fun i => (ev_numericalClass_mapRange (D i) Z).symm⟩⟩

end Proper

/-- On a proper variety `X` over an algebraically closed field of characteristic zero, `N₁(X)` is
finite dimensional and the Cartier evaluations `z ↦ (z · E)` span its dual. Every independent
set of them extends to a basis of the dual. For a basis `(D i)ᵢ` of Cartier evaluations, the
coordinate map `Φ = (z ↦ (z · D i))ᵢ : N₁(X) → ℝ^ι` is a linear homeomorphism for the numerical
topology. `Φ⁻¹(ℤ^ι)` is a closed discrete subgroup, `Φ` restricts to an isomorphism of it onto
`ℤ^ι`, and it contains the class of every integral 1-cycle. The set of classes of integral
1-cycles is countable. -/
@[mmp "lem_mmp_foundation_char_zero_proper_numerical_coordinates"]
public theorem NumericalCurveClasses.exists_cartier_coordinates_of_isProperVariety
    [IsAlgClosed k] [CharZero k] (sX : X ⟶ Spec (.of k)) [IsProperVariety k sX] :
    FiniteDimensional ℝ (NumericalCurveClasses sX) ∧
    Submodule.span ℝ (Set.range fun E : X.CartierDivisor =>
        (NumericalCurveClasses.intersectionNumber (sX := sX) (KCartierDivisor.ofCartier ℝ E))) =
      ⊤ ∧
    (∀ s : Set X.CartierDivisor,
      LinearIndepOn ℝ (fun E : X.CartierDivisor =>
        NumericalCurveClasses.intersectionNumber (sX := sX) (KCartierDivisor.ofCartier ℝ E)) s →
      ∃ t : Set X.CartierDivisor, s ⊆ t ∧
        LinearIndepOn ℝ (fun E : X.CartierDivisor =>
          NumericalCurveClasses.intersectionNumber (sX := sX) (KCartierDivisor.ofCartier ℝ E)) t ∧
        Submodule.span ℝ ((fun E : X.CartierDivisor =>
          NumericalCurveClasses.intersectionNumber (sX := sX) (KCartierDivisor.ofCartier ℝ E)) ''
            t) = ⊤) ∧
    (∀ {ι : Type*} (D : ι → X.CartierDivisor),
      LinearIndependent ℝ (fun i =>
        NumericalCurveClasses.intersectionNumber (sX := sX) (KCartierDivisor.ofCartier ℝ (D i))) →
      Submodule.span ℝ (Set.range fun i =>
        NumericalCurveClasses.intersectionNumber (sX := sX) (KCartierDivisor.ofCartier ℝ (D i))) =
          ⊤ →
      (∃ Φ : NumericalCurveClasses sX ≃L[ℝ] (ι → ℝ),
        (Φ : NumericalCurveClasses sX →ₗ[ℝ] ι → ℝ) = LinearMap.pi fun i =>
          NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ (D i))) ∧
      IsClosed ((AddSubgroup.comap (LinearMap.pi fun i =>
          NumericalCurveClasses.intersectionNumber (sX := sX)
            (KCartierDivisor.ofCartier ℝ (D i))).toAddMonoidHom
          (AddMonoidHom.compLeft (Int.castAddHom ℝ) ι).range : Set (NumericalCurveClasses sX))) ∧
      DiscreteTopology (AddSubgroup.comap (LinearMap.pi fun i =>
          NumericalCurveClasses.intersectionNumber (sX := sX)
            (KCartierDivisor.ofCartier ℝ (D i))).toAddMonoidHom
          (AddMonoidHom.compLeft (Int.castAddHom ℝ) ι).range) ∧
      (∃ e : AddSubgroup.comap (LinearMap.pi fun i =>
          NumericalCurveClasses.intersectionNumber (sX := sX)
            (KCartierDivisor.ofCartier ℝ (D i))).toAddMonoidHom
          (AddMonoidHom.compLeft (Int.castAddHom ℝ) ι).range ≃+ (ι → ℤ),
        ∀ z i, ((e z i : ℤ) : ℝ) =
          NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ (D i))
            (z : NumericalCurveClasses sX)) ∧
      ∀ Z : OneCycle ℤ sX,
        OneCycle.numericalClass sX (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero Z) ∈
          AddSubgroup.comap (LinearMap.pi fun i =>
            NumericalCurveClasses.intersectionNumber (sX := sX)
              (KCartierDivisor.ofCartier ℝ (D i))).toAddMonoidHom
            (AddMonoidHom.compLeft (Int.castAddHom ℝ) ι).range) ∧
    (Set.range fun Z : OneCycle ℤ sX =>
      OneCycle.numericalClass sX
        (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero Z)).Countable := by
  have hspan : Submodule.span ℝ (Set.range (ev sX)) = ⊤ := span_range_ev
  have hext : ∀ s : Set X.CartierDivisor, LinearIndepOn ℝ (ev sX) s →
      ∃ t : Set X.CartierDivisor, s ⊆ t ∧ LinearIndepOn ℝ (ev sX) t ∧
        Submodule.span ℝ (ev sX '' t) = ⊤ := by
    intro s hs
    obtain ⟨b, -, hsb, hspanb, hb⟩ := exists_linearIndepOn_extension hs (Set.subset_univ s)
    refine ⟨b, hsb, hb, eq_top_iff.mpr ?_⟩
    rwa [← hspan, Submodule.span_le, ← Set.image_univ]
  refine ⟨finiteDimensional_numericalCurveClasses sX, hspan, hext,
    fun D hli hspanD => (finite_and_exists_coordinateEquiv_and_lattice D hli hspanD).2, ?_⟩
  obtain ⟨t, -, ht, htspan⟩ := hext ∅ (linearIndepOn_empty ℝ _)
  have hspant : Submodule.span ℝ (Set.range fun i : t => ev sX (i : X.CartierDivisor)) = ⊤ := by
    rw [← htspan, Set.image_eq_range]
  obtain ⟨hfin, -, -, -, ⟨e, -⟩, hmem⟩ :=
    finite_and_exists_coordinateEquiv_and_lattice (Subtype.val : t → X.CartierDivisor) ht hspant
  have hcount : Countable (AddSubgroup.comap
      (LinearMap.pi fun i : t => ev sX (i : X.CartierDivisor)).toAddMonoidHom
      (AddMonoidHom.compLeft (Int.castAddHom ℝ) t).range) :=
    Countable.of_equiv _ e.toEquiv.symm
  exact (Set.countable_coe_iff.mp hcount).mono (Set.range_subset_iff.mpr hmem)

end MMP.Mori
