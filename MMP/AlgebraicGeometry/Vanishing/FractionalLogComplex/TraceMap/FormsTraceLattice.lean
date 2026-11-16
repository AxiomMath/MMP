module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.TraceMap.FormsTraceAtDivisor
public import MMP.RingTheory.Kaehler.LogLattice

/-!
# The trace of forms lands in the lattices of a prime divisor

The logarithmic adapted basis `t⁻¹ dt, dx₁, …, dxₘ` of `Ω_{K/k}` at a prime divisor `E` lies in
the logarithmic lattice of `𝒪_{X,E}`, and the regular adapted basis `dt, dx₁, …, dxₘ` in its
regular lattice. Hence the conclusions of
`MMP.FourfoldProofs.FractionalLogComplexProof.formsTrace_repr_logBasis_mem_range` and
`MMP.FourfoldProofs.FractionalLogComplexProof.formsTrace_repr_regBasis_mem_range`, integral
coordinates in an adapted basis, are memberships of the trace in the wedges of these lattices,
which do not depend on a basis.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.formsTrace_mem_wedgeSpan_logLattice`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.formsTrace_mem_wedgeSpan_regLattice`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing KaehlerDifferential

namespace MMP.FourfoldProofs.FractionalLogComplexProof

universe u

section Bases

variable (k : Type u) [Field k] {A K : Type u} [CommRing A] [Field K] [Algebra k A] [Algebra k K]
  [Algebra A K] [IsScalarTower k A K] [IsFractionRing A K]

/-- The logarithmic adapted basis lies in the logarithmic lattice. -/
theorem logBasis_mem_logLattice [IsLocalRing A] {m : ℕ} {t : A} (x : Fin m → A)
    (bA : Module.Basis (Fin (m + 1)) A Ω[A⁄k])
    (hbA : ∀ i, bA i = D k A ((Fin.cons t x : Fin (m + 1) → A) i)) (ht : algebraMap A K t ≠ 0)
    (i : Fin (m + 1)) : logBasis k bA ht i ∈ logLattice k A (L := K) := by
  refine Fin.cases ?_ (fun l => ?_) i
  · rw [logBasis_zero, hbA, Fin.cons_zero, KaehlerDifferential.map_D]
    exact inv_smul_D_mem_logLattice t
  · rw [logBasis_succ, hbA, Fin.cons_succ, KaehlerDifferential.map_D]
    exact D_mem_logLattice (x l)

/-- The regular adapted basis lies in the regular lattice. -/
theorem regBasis_mem_regLattice {m : ℕ} (y : Fin m → A)
    (bA : Module.Basis (Fin m) A Ω[A⁄k]) (hbA : ∀ i, bA i = D k A (y i)) (i : Fin m) :
    regBasis k (K := K) bA i ∈ regLattice k A (L := K) := by
  rw [regBasis_apply, hbA, KaehlerDifferential.map_D]
  exact D_mem_regLattice (y i)

end Bases

variable {k : Type u} [Field k] [CharZero k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (f : Y ⟶ X) [IsIntegral X] [IsIntegral Y] [IsFinite f] [Surjective f]
  [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]

/-- **The trace lies in the wedges of the logarithmic lattice** of a prime divisor, under the
hypotheses of `MMP.FourfoldProofs.FractionalLogComplexProof.formsTrace_repr_logBasis_mem_range`. -/
theorem formsTrace_mem_wedgeSpan_logLattice (E : MMP.Mori.PrimeDivisor X) (W : X.affineOpens)
    (hEW : E.genericPoint ∈ (W : X.Opens)) (t : Γ(X, W))
    (ht : maximalIdeal E.localRing =
      Ideal.span {X.presheaf.germ (W : X.Opens) E.genericPoint hEW t})
    {m : ℕ} (x : Fin m → E.localRing)
    (bA : letI := MMP.Mori.stalkAlgebra sX E.genericPoint
      Module.Basis (Fin (m + 1)) E.localRing Ω[E.localRing⁄k])
    (hbA : letI := MMP.Mori.stalkAlgebra sX E.genericPoint
      ∀ i, bA i = D k E.localRing ((Fin.cons (X.presheaf.germ (W : X.Opens) E.genericPoint hEW t)
        x : Fin (m + 1) → E.localRing) i))
    (htK : algebraMap E.localRing X.functionField
      (X.presheaf.germ (W : X.Opens) E.genericPoint hEW t) ≠ 0)
    (p : ℕ) (ω : letI := MMP.Mori.functionFieldAlgebra (f ≫ sX)
      ⋀[Y.functionField]^p Ω[Y.functionField⁄k])
    (hω : ∀ y : Y, f y = E.genericPoint →
      letI := MMP.Mori.stalkAlgebra (f ≫ sX) y
      letI := MMP.Mori.functionFieldAlgebra (f ≫ sX)
      haveI := MMP.Mori.isScalarTower_stalk_functionField (f ≫ sX) y
      haveI : Nonempty (W : X.Opens) := ⟨⟨_, hEW⟩⟩
      ∃ (s : Y.presheaf.stalk y) (_ : maximalIdeal (Y.presheaf.stalk y) = Ideal.span {s})
        (yv : Fin m → Y.presheaf.stalk y)
        (bR : Module.Basis (Fin (m + 1)) (Y.presheaf.stalk y) Ω[Y.presheaf.stalk y⁄k])
        (_ : ∀ i, bR i = D k (Y.presheaf.stalk y)
          ((Fin.cons s yv : Fin (m + 1) → Y.presheaf.stalk y) i))
        (ρ : Y.presheaf.stalk y) (_ : ρ ∈ maximalIdeal (Y.presheaf.stalk y))
        (η : ⋀[Y.functionField]^p Ω[Y.functionField⁄k])
        (_ : η ∈ wedgeSpan (Y.presheaf.stalk y) (Submodule.span (Y.presheaf.stalk y)
          (Set.range (Fin.cons
            ((algebraMap (Y.presheaf.stalk y) Y.functionField s)⁻¹ •
              D k Y.functionField (algebraMap (Y.presheaf.stalk y) Y.functionField s))
            fun j => D k Y.functionField (algebraMap (Y.presheaf.stalk y) Y.functionField (yv j))
              : Fin (m + 1) → Ω[Y.functionField⁄k]))) p),
        AlgebraicGeometry.functionFieldMap f (X.germToFunctionField (W : X.Opens) t) • ω =
          algebraMap (Y.presheaf.stalk y) Y.functionField ρ • η) :
    letI := MMP.Mori.stalkAlgebra sX E.genericPoint
    letI := MMP.Mori.functionFieldAlgebra sX
    letI := MMP.Mori.functionFieldAlgebra (f ≫ sX)
    letI := MMP.Mori.functionFieldMapAlgebra f
    haveI := MMP.Mori.isScalarTower_functionFieldMap sX f
    haveI := MMP.Mori.isScalarTower_stalk_functionField sX E.genericPoint
    haveI := finiteDimensional_functionFieldMap f
    haveI := isSeparable_functionFieldMap sX f
    formsTrace k X.functionField Y.functionField p ω ∈
      wedgeSpan E.localRing (logLattice k E.localRing (L := X.functionField)) p := by
  let := MMP.Mori.stalkAlgebra sX E.genericPoint
  let := MMP.Mori.functionFieldAlgebra sX
  let := MMP.Mori.functionFieldAlgebra (f ≫ sX)
  let := MMP.Mori.functionFieldMapAlgebra f
  have := MMP.Mori.isScalarTower_functionFieldMap sX f
  have := MMP.Mori.isScalarTower_stalk_functionField sX E.genericPoint
  have := finiteDimensional_functionFieldMap f
  have := isSeparable_functionFieldMap sX f
  refine wedgeSpan_mono ?_ p (mem_wedgeSpan_of_repr_mem (logBasis k bA htK) _
    (formsTrace_repr_logBasis_mem_range sX f E W hEW t ht x bA hbA htK p ω hω))
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact logBasis_mem_logLattice k x bA hbA htK i

/-- **The trace lies in the wedges of the regular lattice** of a prime divisor, under the
hypotheses of `MMP.FourfoldProofs.FractionalLogComplexProof.formsTrace_repr_regBasis_mem_range`. -/
theorem formsTrace_mem_wedgeSpan_regLattice (E : MMP.Mori.PrimeDivisor X) (W : X.affineOpens)
    (hEW : E.genericPoint ∈ (W : X.Opens)) (t : Γ(X, W))
    (ht : maximalIdeal E.localRing =
      Ideal.span {X.presheaf.germ (W : X.Opens) E.genericPoint hEW t})
    {m : ℕ} (x : Fin m → E.localRing)
    (bA : letI := MMP.Mori.stalkAlgebra sX E.genericPoint
      Module.Basis (Fin (m + 1)) E.localRing Ω[E.localRing⁄k])
    (hbA : letI := MMP.Mori.stalkAlgebra sX E.genericPoint
      ∀ i, bA i = D k E.localRing ((Fin.cons (X.presheaf.germ (W : X.Opens) E.genericPoint hEW t)
        x : Fin (m + 1) → E.localRing) i))
    (htK : algebraMap E.localRing X.functionField
      (X.presheaf.germ (W : X.Opens) E.genericPoint hEW t) ≠ 0)
    (p : ℕ) (ω : letI := MMP.Mori.functionFieldAlgebra (f ≫ sX)
      ⋀[Y.functionField]^p Ω[Y.functionField⁄k])
    (hω : ∀ y : Y, f y = E.genericPoint →
      letI := MMP.Mori.stalkAlgebra (f ≫ sX) y
      letI := MMP.Mori.functionFieldAlgebra (f ≫ sX)
      haveI := MMP.Mori.isScalarTower_stalk_functionField (f ≫ sX) y
      haveI : Nonempty (W : X.Opens) := ⟨⟨_, hEW⟩⟩
      ∃ (s : Y.presheaf.stalk y) (_ : maximalIdeal (Y.presheaf.stalk y) = Ideal.span {s})
        (yv : Fin m → Y.presheaf.stalk y)
        (bR : Module.Basis (Fin (m + 1)) (Y.presheaf.stalk y) Ω[Y.presheaf.stalk y⁄k])
        (_ : ∀ i, bR i = D k (Y.presheaf.stalk y)
          ((Fin.cons s yv : Fin (m + 1) → Y.presheaf.stalk y) i))
        (ρ : Y.presheaf.stalk y) (η : ⋀[Y.functionField]^p Ω[Y.functionField⁄k])
        (_ : η ∈ wedgeSpan (Y.presheaf.stalk y) (Submodule.span (Y.presheaf.stalk y)
          (Set.range fun j => D k Y.functionField (algebraMap (Y.presheaf.stalk y) Y.functionField
            ((Fin.cons s yv : Fin (m + 1) → Y.presheaf.stalk y) j)))) p),
        ω = algebraMap (Y.presheaf.stalk y) Y.functionField ρ • η) :
    letI := MMP.Mori.stalkAlgebra sX E.genericPoint
    letI := MMP.Mori.functionFieldAlgebra sX
    letI := MMP.Mori.functionFieldAlgebra (f ≫ sX)
    letI := MMP.Mori.functionFieldMapAlgebra f
    haveI := MMP.Mori.isScalarTower_functionFieldMap sX f
    haveI := MMP.Mori.isScalarTower_stalk_functionField sX E.genericPoint
    haveI := finiteDimensional_functionFieldMap f
    haveI := isSeparable_functionFieldMap sX f
    formsTrace k X.functionField Y.functionField p ω ∈
      wedgeSpan E.localRing (regLattice k E.localRing (L := X.functionField)) p := by
  let := MMP.Mori.stalkAlgebra sX E.genericPoint
  let := MMP.Mori.functionFieldAlgebra sX
  let := MMP.Mori.functionFieldAlgebra (f ≫ sX)
  let := MMP.Mori.functionFieldMapAlgebra f
  have := MMP.Mori.isScalarTower_functionFieldMap sX f
  have := MMP.Mori.isScalarTower_stalk_functionField sX E.genericPoint
  have := finiteDimensional_functionFieldMap f
  have := isSeparable_functionFieldMap sX f
  refine wedgeSpan_mono ?_ p (mem_wedgeSpan_of_repr_mem (regBasis k (K := X.functionField) bA) _
    (formsTrace_repr_regBasis_mem_range sX f E W hEW t ht x bA hbA htK p ω hω))
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact regBasis_mem_regLattice k _ bA hbA i

end MMP.FourfoldProofs.FractionalLogComplexProof
