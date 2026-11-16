module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.AdaptedBases

/-!
# Regular and logarithmic lattices of rational forms over a local ring

Let `R` be a local `k`-algebra with fraction field `L`. Inside `Ω_{L/k}` the *regular lattice* is
the `R`-span of the differentials `d a`, `a ∈ R`, and the *logarithmic lattice* the `R`-span of
the logarithmic differentials `a⁻¹ d a`, `a ∈ R` (with `0⁻¹ = 0`). Every differential `d a` is
logarithmic: `d a = a · a⁻¹ d a` for a unit `a`, and otherwise `1 - a` is a unit. The pull-back of
a logarithmic form along a local homomorphism into `R` is therefore always logarithmic.

When `R` is a discrete valuation ring, smooth and essentially of finite type over a perfect
field, with uniformizer `s`, the logarithmic lattice is spanned by `s⁻¹ ds` and a basis of
`Ω_{R/k}` containing `ds`, so a `p`-fold wedge of logarithmic forms has at most a simple pole
along `s`: multiplied by any element of the maximal ideal it becomes a wedge of regular forms.
This is the computation `t^a dt/t` with `a ≥ 1` of the pull-back of the fractional logarithmic
complex to a cover.

## Main definitions

* `MMP.FourfoldProofs.FractionalLogComplexProof.regLattice`: the regular lattice.
* `MMP.FourfoldProofs.FractionalLogComplexProof.logLattice`: the logarithmic lattice.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.D_mem_logLattice`: differentials are logarithmic.
* `MMP.FourfoldProofs.FractionalLogComplexProof.mem_wedgeSpan_of_repr_mem`: forms with integral
  coordinates lie in the wedge lattice of the basis.
* `MMP.FourfoldProofs.FractionalLogComplexProof.smul_mem_wedgeSpan_regLattice`: the maximal ideal
  times the wedges of logarithmic forms lies in the wedges of regular forms.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.67
-/

@[expose] public section

open KaehlerDifferential IsLocalRing

namespace MMP.FourfoldProofs.FractionalLogComplexProof

universe u

section Coordinates

variable {R L M : Type*} [CommRing R] [CommRing L] [Algebra R L] [AddCommGroup M] [Module L M]
  [Module R M] [IsScalarTower R L M]

/-- **Forms with integral coordinates.** A form whose coordinates in the wedges of a basis `b` lie
in `R` is in the wedge lattice of the `R`-span of `b`. -/
theorem mem_wedgeSpan_of_repr_mem {ι : Type*} [LinearOrder ι] (b : Module.Basis ι L M) {p : ℕ}
    (ω : ⋀[L]^p M) (h : ∀ S, (b.exteriorPower p).repr ω S ∈ (algebraMap R L).range) :
    ω ∈ wedgeSpan R (Submodule.span R (Set.range b)) p := by
  classical
  rw [← (b.exteriorPower p).linearCombination_repr ω, Finsupp.linearCombination_apply]
  refine Submodule.finsuppSum_mem _ _ _ _ fun S _ => ?_
  obtain ⟨r, hr⟩ := h S
  rw [← hr, algebraMap_smul]
  refine Submodule.smul_mem _ _ ?_
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
  exact ιMulti_mem_wedgeSpan fun i => Submodule.subset_span ⟨_, rfl⟩

/-- **Coordinates of an ideal multiple of the wedge lattice.** If the forms of `N` have their
coordinates in `R`, the coordinates of the elements of `I • ⋀^p N` lie in `I`. -/
theorem exists_mem_ideal_repr_eq {ι : Type*} [LinearOrder ι] (b : Module.Basis ι L M)
    (N : Submodule R M) (hN : ∀ v ∈ N, ∀ j, b.repr v j ∈ (algebraMap R L).range) (I : Ideal R)
    {p : ℕ} {ω : ⋀[L]^p M} (hω : ω ∈ I • wedgeSpan R N p) (S : Set.powersetCard ι p) :
    ∃ r ∈ I, algebraMap R L r = (b.exteriorPower p).repr ω S := by
  refine Submodule.smul_induction_on
    (p := fun ω => ∃ r ∈ I, algebraMap R L r = (b.exteriorPower p).repr ω S) hω ?_ ?_
  · intro m hm η hη
    obtain ⟨r, hr⟩ := exteriorPower_repr_mem_range_of_mem_span b N hN hη S
    refine ⟨m * r, I.mul_mem_right r hm, ?_⟩
    rw [← algebraMap_smul L m η, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hr]
  · intro x y hx hy
    obtain ⟨r, hr, hrx⟩ := hx
    obtain ⟨r', hr', hry⟩ := hy
    exact ⟨r + r', I.add_mem hr hr', by rw [map_add, hrx, hry, map_add, Finsupp.add_apply]⟩

end Coordinates

section Lattices

variable (k : Type u) [Field k] (R : Type u) {L : Type u} [CommRing R] [Field L] [Algebra k R]
  [Algebra k L] [Algebra R L] [IsScalarTower k R L]

/-- **The regular lattice** of `Ω_{L/k}` over `R`: the `R`-span of the differentials `d a`,
`a ∈ R`. -/
noncomputable def regLattice : Submodule R Ω[L⁄k] :=
  Submodule.span R (Set.range fun a : R => D k L (algebraMap R L a))

/-- **The logarithmic lattice** of `Ω_{L/k}` over `R`: the `R`-span of the logarithmic
differentials `a⁻¹ d a`, `a ∈ R`. -/
noncomputable def logLattice : Submodule R Ω[L⁄k] :=
  Submodule.span R (Set.range fun a : R => (algebraMap R L a)⁻¹ • D k L (algebraMap R L a))

variable {k R}

/-- The differential `d a` of an element `a ∈ R` lies in the regular lattice. -/
theorem D_mem_regLattice (a : R) : D k L (algebraMap R L a) ∈ regLattice k R :=
  Submodule.subset_span ⟨a, rfl⟩

/-- The logarithmic differential `a⁻¹ d a` of an element `a ∈ R` lies in the logarithmic
lattice. -/
theorem inv_smul_D_mem_logLattice (a : R) :
    (algebraMap R L a)⁻¹ • D k L (algebraMap R L a) ∈ logLattice k R :=
  Submodule.subset_span ⟨a, rfl⟩

/-- **Differentials are logarithmic** over a local ring: the differential `d a` of every element
`a ∈ R` lies in the logarithmic lattice. -/
theorem D_mem_logLattice [IsLocalRing R] (a : R) : D k L (algebraMap R L a) ∈ logLattice k R := by
  have key : ∀ b : R, IsUnit b → D k L (algebraMap R L b) ∈ logLattice k R := by
    intro b hb
    rw [show D k L (algebraMap R L b) = b • ((algebraMap R L b)⁻¹ • D k L (algebraMap R L b)) by
      rw [← algebraMap_smul L b, smul_smul, mul_inv_cancel₀ (hb.map (algebraMap R L)).ne_zero,
        one_smul]]
    exact Submodule.smul_mem _ _ (inv_smul_D_mem_logLattice b)
  rcases isUnit_or_isUnit_one_sub_self a with h | h
  · exact key a h
  · have h1 := key _ h
    rwa [map_sub, map_one, map_sub, Derivation.map_one_eq_zero, zero_sub, neg_mem_iff] at h1

/-- Over a local ring the regular lattice is contained in the logarithmic lattice. -/
theorem regLattice_le_logLattice [IsLocalRing R] : regLattice k R ≤ logLattice (L := L) k R :=
  Submodule.span_le.2 <| Set.range_subset_iff.2 D_mem_logLattice

/-- The image in `Ω_{L/k}` of a form of `Ω_{R/k}` lies in the `R`-span of the logarithmic adapted
basis. -/
theorem map_mem_span_logBasis [IsFractionRing R L] {n : ℕ}
    (c : Module.Basis (Fin (n + 1)) R Ω[R⁄k]) {s : R} (hsL : algebraMap R L s ≠ 0)
    (ω : Ω[R⁄k]) :
    KaehlerDifferential.map k k R L ω ∈ Submodule.span R (Set.range (logBasis k c hsL)) := by
  refine Submodule.span_le.2 ?_ (map_mem_span_of_basis k (L := L) c ω)
  rintro _ ⟨i, rfl⟩
  refine Fin.cases ?_ (fun i => ?_) i
  · rw [Function.comp_apply, show KaehlerDifferential.map k k R L (c 0) = s • logBasis k c hsL 0 by
      rw [logBasis_zero, ← algebraMap_smul L s, smul_smul, mul_inv_cancel₀ hsL, one_smul]]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
  · rw [Function.comp_apply, ← logBasis_succ k c hsL i]
    exact Submodule.subset_span ⟨_, rfl⟩

/-- Over a discrete valuation ring with uniformizer `s`, the logarithmic lattice lies in the
`R`-span of the logarithmic adapted basis built from a basis of `Ω_{R/k}` starting with `ds`. -/
theorem logLattice_le_span_logBasis [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R L]
    {n : ℕ} (c : Module.Basis (Fin (n + 1)) R Ω[R⁄k]) {s : R} (hs : Irreducible s)
    (hsL : algebraMap R L s ≠ 0) (hc : c 0 = D k R s) :
    logLattice k R ≤ Submodule.span R (Set.range (logBasis k c hsL)) := by
  rw [logLattice, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  by_cases ha : a = 0
  · simp [ha]
  obtain ⟨e, v, hav⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hs
  have haL : algebraMap R L a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R L)).2 ha
  have key := inv_smul_D_eq_of_eq_mul_pow k (A := R) (B := R) (L := L) v.isUnit
    (t := a) (s := s) (e := e) hav (inv_mul_cancel₀ hsL) (inv_mul_cancel₀ haL)
  change (algebraMap R L a)⁻¹ • D k L (algebraMap R L a) ∈ _
  rw [key]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
  · refine Submodule.subset_span ⟨0, ?_⟩
    rw [logBasis_zero, hc, KaehlerDifferential.map_D]
  · rw [← KaehlerDifferential.map_D k k R L]
    exact map_mem_span_logBasis c hsL _

/-- If the coordinates of a `p`-form in the wedges of the logarithmic adapted basis lie in `R`, so
do the coordinates of its multiple by `q * s` in the wedges of the regular adapted basis. -/
theorem regBasis_repr_smul_mem_range [IsFractionRing R L] {n : ℕ}
    (c : Module.Basis (Fin (n + 1)) R Ω[R⁄k]) {s : R} (hsL : algebraMap R L s ≠ 0) {p : ℕ}
    {ω : ⋀[L]^p (Ω[L⁄k])}
    (hω : ∀ S, ((logBasis k c hsL).exteriorPower p).repr ω S ∈ (algebraMap R L).range) (q : R)
    (S : Set.powersetCard (Fin (n + 1)) p) :
    ((regBasis k (K := L) c).exteriorPower p).repr ((q * s) • ω) S ∈ (algebraMap R L).range := by
  classical
  let w : Fin (n + 1) → Lˣ := fun i => if i = 0 then (Units.mk0 _ hsL)⁻¹ else 1
  have hw : logBasis k (K := L) c hsL = (regBasis k c).unitsSMul w := rfl
  obtain ⟨r', hr'⟩ := hω S
  rw [← algebraMap_smul L (q * s) ω, map_smul, Finsupp.smul_apply, smul_eq_mul,
    exteriorPower_repr_unitsSMul _ w, ← hw, ← hr']
  set σ := Set.powersetCard.ofFinEmbEquiv.symm S
  by_cases h0 : ∃ j, σ j = 0
  · obtain ⟨j₀, hj₀⟩ := h0
    have : ∏ j, (w (σ j) : L) = (algebraMap R L s)⁻¹ := by
      rw [Finset.prod_eq_single j₀]
      · simp [w, hj₀]
      · intro j _ hj
        have : σ j ≠ 0 := fun h => hj (σ.injective (h.trans hj₀.symm))
        simp [w, this]
      · simp
    refine ⟨q * r', ?_⟩
    rw [this]
    simp only [map_mul]
    field_simp
  · push Not at h0
    have : ∏ j, (w (σ j) : L) = 1 := Finset.prod_eq_one fun j _ => by simp [w, h0 j]
    refine ⟨q * s * r', ?_⟩
    rw [this]
    simp only [map_mul]
    ring

/-- The `R`-span of the regular adapted basis built from a basis of differentials `d yᵢ` of
`Ω_{R/k}` lies in the regular lattice. -/
theorem span_regBasis_le_regLattice [IsFractionRing R L] {n : ℕ}
    (c : Module.Basis (Fin n) R Ω[R⁄k]) {y : Fin n → R} (hc : ∀ i, c i = D k R (y i)) :
    Submodule.span R (Set.range (regBasis k (K := L) c)) ≤ regLattice k R :=
  Submodule.span_le.2 <| Set.range_subset_iff.2 fun i => by
    rw [regBasis_apply, hc, KaehlerDifferential.map_D]
    exact D_mem_regLattice _

/-- **A simple pole at most.** Over a discrete valuation ring `R`, smooth and essentially of
finite type over a perfect field `k`, an element of the maximal ideal times a wedge of
logarithmic forms is a wedge of regular forms. -/
theorem smul_mem_wedgeSpan_regLattice [IsDomain R] [IsDiscreteValuationRing R]
    [IsFractionRing R L] [PerfectField k] [Algebra.FormallySmooth k R] [Algebra.EssFiniteType k R]
    [Module.Free R Ω[R⁄k]] [Module.Finite R Ω[R⁄k]] {m : R} (hm : m ∈ maximalIdeal R) {p : ℕ}
    {ω : ⋀[L]^p (Ω[L⁄k])} (hω : ω ∈ wedgeSpan R (logLattice k R) p) :
    m • ω ∈ wedgeSpan R (regLattice k R) p := by
  obtain ⟨s, hs⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hms := (IsDiscreteValuationRing.irreducible_iff_uniformizer s).1 hs
  have hsL : algebraMap R L s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R L)).2 hs.ne_zero
  obtain ⟨n, y, c, hc⟩ := exists_basis_D_cons k (Module.Free.chooseBasis R Ω[R⁄k]) hms hs.ne_zero
  obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 (hms ▸ hm)
  have hlog := logLattice_le_span_logBasis c hs hsL (by rw [hc, Fin.cons_zero])
  exact wedgeSpan_mono (span_regBasis_le_regLattice c hc) p <| mem_wedgeSpan_of_repr_mem _ _ <|
    regBasis_repr_smul_mem_range c hsL
      (repr_mem_range_of_mem_wedgeSpan _ (wedgeSpan_mono hlog p hω)) q

end Lattices

end MMP.FourfoldProofs.FractionalLogComplexProof
