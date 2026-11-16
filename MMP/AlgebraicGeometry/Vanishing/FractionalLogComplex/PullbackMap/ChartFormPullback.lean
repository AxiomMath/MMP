module

public import MMP.RingTheory.Kaehler.LogLattice
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Place.ChartForms
public import MMP.AlgebraicGeometry.Morphisms.PointLocalHom

/-!
# Pull-backs of chart combinations at a point of a cover

Let `g : Y ⟶ X` be a dominant morphism of integral schemes over `k`, `y ∈ Y` with `g y = x`, and
`R = 𝒪_{Y,y}`. The pull-back of a rational chart form `tₗ⁻¹ dtₗ` (`l < r`), resp. `dtₗ`, of a
chart of `X` through `x` is `Tₗ⁻¹ dTₗ`, resp. `dTₗ`, for the image `Tₗ ∈ R` of `tₗ` under the local
homomorphism `𝒪_{X,x} → R`: a logarithmic form of `R`, and a regular one for `l ≥ r`.

So a combination `∑_q e_q β_q` of wedges of such forms with coefficients `e_q ∈ R` lies in the
wedges of the logarithmic lattice of `R`; if the coefficients lie in the maximal ideal, it lies in
the maximal ideal times these wedges, and, when `R` is a discrete valuation ring smooth over a
perfect field, also in the wedges of the regular lattice (a logarithmic pole is cancelled by any
element of the maximal ideal); and if `r = 0` it lies in the wedges of the regular lattice.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.mem_lattices_of_eq_sum`: the lattices of a
  combination.
* `MMP.FourfoldProofs.FractionalLogComplexProof.map_chartForm_eq`: the pull-back of a chart form.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite KaehlerDifferential TopologicalSpace IsLocalRing

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology

universe u

section Algebra

variable (k : Type u) [Field k] {R : Type u} {L : Type u} [CommRing R] [Field L] [Algebra k R]
  [Algebra k L] [Algebra R L] [IsScalarTower k R L]

/-- **The lattices of a combination of wedges of logarithmic forms.** Let `τₗ` be logarithmic
forms of `R`, regular for `l ≥ r`, and `β = ∑_q e_q ∧_j τ_{κ q j}` with `e_q ∈ R`. Then `β` lies in
the wedges of the logarithmic lattice; if every `e_q` lies in the maximal ideal, `β` lies in the
maximal ideal times these wedges, and in the wedges of the regular lattice over a discrete
valuation ring smooth over a perfect field; and if `r = 0`, `β` lies in the wedges of the regular
lattice. -/
theorem mem_lattices_of_eq_sum [IsLocalRing R] {n r p : ℕ} (τ : Fin n → Ω[L⁄k])
    (hlog : ∀ l, τ l ∈ logLattice k R) (hreg : ∀ l : Fin n, r ≤ l → τ l ∈ regLattice k R)
    {ι : Type*} (s : Finset ι) (e : ι → R) (κ : ι → Fin p → Fin n) {β : ⋀[L]^p (Ω[L⁄k])}
    (hβ : β = ∑ q ∈ s, algebraMap R L (e q) • exteriorPower.ιMulti L p (τ ∘ κ q)) :
    β ∈ wedgeSpan R (logLattice k R) p ∧
      (r = 0 → β ∈ wedgeSpan R (regLattice k R) p) ∧
      ((∀ q ∈ s, e q ∈ maximalIdeal R) →
        β ∈ maximalIdeal R • wedgeSpan R (logLattice k R) p ∧
          ([IsDomain R] → [IsDiscreteValuationRing R] → [IsFractionRing R L] →
            [PerfectField k] → [Algebra.FormallySmooth k R] → [Algebra.EssFiniteType k R] →
            [Module.Free R Ω[R⁄k]] → [Module.Finite R Ω[R⁄k]] →
              β ∈ wedgeSpan R (regLattice k R) p)) := by
  subst hβ
  have hw : ∀ q, exteriorPower.ιMulti L p (τ ∘ κ q) ∈ wedgeSpan R (logLattice k R) p :=
    fun q => ιMulti_mem_wedgeSpan fun j => hlog _
  refine ⟨Submodule.sum_mem _ fun q _ => ?_, fun hr => Submodule.sum_mem _ fun q _ => ?_,
    fun hm => ⟨Submodule.sum_mem _ fun q hq => ?_, ?_⟩⟩
  · rw [algebraMap_smul]
    exact Submodule.smul_mem _ _ (hw q)
  · rw [algebraMap_smul]
    exact Submodule.smul_mem _ _ (ιMulti_mem_wedgeSpan fun j => hreg _ (hr ▸ Nat.zero_le _))
  · rw [algebraMap_smul]
    exact Submodule.smul_mem_smul (hm q hq) (hw q)
  · intros
    refine Submodule.sum_mem _ fun q hq => ?_
    rw [algebraMap_smul]
    exact smul_mem_wedgeSpan_regLattice (hm q hq) (hw q)

end Algebra

section Pullback

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- **The pull-back of a rational chart form** along a dominant `g : Y ⟶ X`: if `g y = x` with
`x ∈ W`, the image of `chartForm sX W t r l` under `Ω[K(X)⁄k] → Ω[K(Y)⁄k]` is `Tₗ⁻¹ dTₗ` if `l < r`
and `dTₗ` if `r ≤ l`, where `Tₗ` is the image of `tₗ` under `𝒪_{X,x} → 𝒪_{Y,y}`. -/
theorem map_chartForm_eq (sX : X ⟶ Spec (.of k)) (g : Y ⟶ X) [IsDominant g] {n : ℕ}
    (W : X.affineOpens) [Nonempty (W : X.Opens)] (t : Fin n → Γ(X, W)) (r : ℕ) (l : Fin n)
    {y : Y} {x : X} (h : g y = x) (hx : x ∈ (W : X.Opens)) :
    letI := MMP.Mori.functionFieldAlgebra sX
    letI := MMP.Mori.functionFieldAlgebra (g ≫ sX)
    letI := MMP.Mori.functionFieldMapAlgebra g
    haveI := MMP.Mori.isScalarTower_functionFieldMap sX g
    KaehlerDifferential.map k k X.functionField Y.functionField (chartForm sX W t r l) =
      (if (l : ℕ) < r then (algebraMap (Y.presheaf.stalk y) Y.functionField
          ((placeHom g h).hom (X.presheaf.germ (W : X.Opens) x hx (t l))))⁻¹ else 1) •
        D k Y.functionField (algebraMap (Y.presheaf.stalk y) Y.functionField
          ((placeHom g h).hom (X.presheaf.germ (W : X.Opens) x hx (t l)))) := by
  let := MMP.Mori.functionFieldAlgebra sX
  let := MMP.Mori.functionFieldAlgebra (g ≫ sX)
  let := MMP.Mori.functionFieldMapAlgebra g
  have := MMP.Mori.isScalarTower_functionFieldMap sX g
  have hT : algebraMap (Y.presheaf.stalk y) Y.functionField
      ((placeHom g h).hom (X.presheaf.germ (W : X.Opens) x hx (t l))) =
      algebraMap X.functionField Y.functionField (X.germToFunctionField W (t l)) := by
    rw [algebraMap_placeHom, Scheme.algebraMap_germ_eq_germToFunctionField]
    rfl
  rw [hT, chartForm, LinearMap.map_smul_of_tower, KaehlerDifferential.map_D,
    ← algebraMap_smul Y.functionField]
  congr 1
  split_ifs <;> simp [map_inv₀]

end Pullback

end MMP.FourfoldProofs.FractionalLogComplexProof
