module

public import MMP.AlgebraicTopology.SingularCohomology.Relative.Excision
/-!
# The long exact sequence of a pair, on cochains

Let `Y` be a space and `B ⊆ U ⊆ Y`. The long exact sequence of the triple `(Y, U, B)`,
```
⋯ → H^p(Y, U) → H^p(Y, B) → H^p(U, B) → H^{p+1}(Y, U) → H^{p+1}(Y, B) → ⋯
```
in singular cohomology with coefficients in the ring `R`, computed as cocycles modulo coboundaries
(`MMP.SingularCochain.relCohomology`). With `B = ∅` (or `B = Y - Y`) it is the
sequence `⋯ → H^p(Y, U) → H^p Y → H^p U → H^{p+1}(Y, U) → ⋯` of the pair `(Y, U)`; for
`U = Y - X` it is the sequence `H^p(Y, Y - X) → H^p Y → H^p(Y - X) → H^{p+1}(Y, Y - X)` used for
Alexander duality (Fulton, §19.1).

The maps are the forgetful map `[φ] ↦ [φ]`, the restriction `[φ] ↦ [φ|_U]`, and the coboundary
`δ [ψ] = [δ χ]` for any cochain `χ` on `Y` extending `ψ` (`relCohomologyDelta_mk`); the
extension by zero (`MMP.SingularCochain.extendCochain`) defines it.

The subset of `U` (as a space) on which the cochains of `U` vanish is any `B'` with
`U ∩ B = B'`, i.e. `subspaceInclusion Y U ⁻¹' B = B'`, so that both `∅` and `(univ : Set U)ᶜ`
can be used.

## Main definitions

* `MMP.SingularCochain.relCohomologyForget`: `H^p(Y, U) → H^p(Y, B)`.
* `MMP.SingularCochain.relCohomologyRestrict`: `H^p(Y, B) → H^p(U, B')`.
* `MMP.SingularCochain.relCohomologyDelta`: `δ : H^p(U, B') → H^{p+1}(Y, U)`.

## Main results

* `MMP.SingularCochain.relCohomologyDelta_mk`: `δ [ψ] = [δ χ]` for `χ|_U = ψ`.
* `MMP.SingularCochain.exact_relCohomologyForget_relCohomologyRestrict`,
  `exact_relCohomologyRestrict_relCohomologyDelta`, `exact_relCohomologyDelta_relCohomologyForget`:
  exactness at `H^p(Y, B)`, `H^p(U, B')`, `H^{p+1}(Y, U)`.
* `MMP.SingularCochain.injective_relCohomologyForget_zero`: `H^0(Y, U) → H^0(Y, B)`
  is injective.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §3.1.
-/

@[expose] public noncomputable section

open CategoryTheory Set

namespace MMP

namespace SingularCochain

open SingularChain

section extend

variable {R : Type*} [CommRing R] {Y : TopCat} {V : Set Y}

/-- Extension by zero of cochains of `V` to cochains of `Y` is additive. -/
lemma extendCochain_add {n : ℕ} (ψ ψ' : Simplex (TopCat.of V) n → R) :
    extendCochain (ψ + ψ') = extendCochain (V := V) ψ + extendCochain ψ' := by
  ext σ
  by_cases h : range σ ⊆ V <;> simp [extendCochain, h]

/-- Extension by zero of cochains of `V` to cochains of `Y` commutes with scalar multiplication. -/
lemma extendCochain_smul {n : ℕ} (r : R) (ψ : Simplex (TopCat.of V) n → R) :
    extendCochain (r • ψ) = r • extendCochain (V := V) ψ := by
  ext σ
  by_cases h : range σ ⊆ V <;> simp [extendCochain, h]

/-- A cochain of `Y` vanishes on `V` if and only if its restriction to `V` is zero. -/
lemma mem_vanishing_iff_cochainPullback_subspaceInclusion_eq_zero {n : ℕ}
    (φ : Simplex Y n → R) :
    φ ∈ vanishing R n V ↔ cochainPullback R (subspaceInclusion Y V) n φ = 0 := by
  constructor
  · intro h
    ext τ
    exact h _ (range_subspaceInclusion_comp τ)
  · intro h σ hσ
    have := congrFun h (liftSimplex σ hσ)
    rwa [cochainPullback_apply, subspaceInclusion_comp_liftSimplex] at this

/-- Two cochains of `Y` with the same restriction to `V` differ by a cochain vanishing on `V`. -/
lemma extendCochain_sub_mem_vanishing {n : ℕ} {ψ : Simplex (TopCat.of V) n → R}
    {χ : Simplex Y n → R} (hχ : cochainPullback R (subspaceInclusion Y V) n χ = ψ) :
    extendCochain ψ - χ ∈ vanishing R n V := by
  rw [mem_vanishing_iff_cochainPullback_subspaceInclusion_eq_zero, map_sub,
    cochainPullback_extendCochain, hχ, sub_self]

/-- The coboundary of a cochain of `Y` whose restriction to `V` is a cocycle is a relative
cocycle of `(Y, V)`. -/
lemma coboundary_mem_relCocycles_of_cochainPullback {n : ℕ} {χ : Simplex Y n → R}
    (hχ : coboundary R n (cochainPullback R (subspaceInclusion Y V) n χ) = 0) :
    coboundary R n χ ∈ relCocycles R V (n + 1) := by
  refine (mem_relCocycles_iff R V (n + 1) _).2 ⟨?_, coboundary_coboundary n χ⟩
  rw [mem_vanishing_iff_cochainPullback_subspaceInclusion_eq_zero, ← coboundary_cochainPullback,
    hχ]

end extend

section pair

variable (R : Type*) [CommRing R] {Y : TopCat} (U : Set Y) {B : Set Y}

/-- The forgetful map `H^p(Y, U) → H^p(Y, B)`, `[φ] ↦ [φ]`, for `B ⊆ U`. -/
def relCohomologyForget (hBU : B ⊆ U) (p : ℕ) : relCohomology R U p →ₗ[R] relCohomology R B p :=
  relCohomologyMap R (𝟙 Y) hBU p

/-- The restriction `H^p(Y, B) → H^p(U, B')`, `[φ] ↦ [φ|_U]`, for `U ∩ B = B'`. -/
def relCohomologyRestrict {B' : Set (TopCat.of U)} (hB' : subspaceInclusion Y U ⁻¹' B = B')
    (p : ℕ) : relCohomology R B p →ₗ[R] relCohomology R B' p :=
  relCohomologyMap R (subspaceInclusion Y U) hB'.symm.subset p

/-- On cocycles: `ψ ↦ δ (extension of ψ by zero)`, a relative cocycle of `(Y, U)`. -/
def relCocyclesDelta (B' : Set (TopCat.of U)) (p : ℕ) :
    relCocycles R B' p →ₗ[R] relCocycles R U (p + 1) where
  toFun ψ := ⟨coboundary R p (extendCochain ψ.1),
    coboundary_mem_relCocycles_of_cochainPullback (by
      rw [cochainPullback_extendCochain]
      exact ((mem_relCocycles_iff R B' p _).1 ψ.2).2)⟩
  map_add' ψ ψ' := Subtype.ext (by
    change coboundary R p (extendCochain (ψ.1 + ψ'.1)) = _
    rw [extendCochain_add, map_add]
    rfl)
  map_smul' r ψ := Subtype.ext (by
    change coboundary R p (extendCochain (r • ψ.1)) = _
    rw [extendCochain_smul, map_smul]
    rfl)

/-- The underlying cochain of `relCocyclesDelta R U B' p ψ` is the coboundary of the extension
of `ψ` by zero. -/
lemma relCocyclesDelta_coe (B' : Set (TopCat.of U)) (p : ℕ) (ψ : relCocycles R B' p) :
    (relCocyclesDelta R U B' p ψ : Simplex Y (p + 1) → R) =
      coboundary R p (extendCochain ψ.1) :=
  rfl

variable {R U}

/-- The coboundary of the extension by zero of a relative coboundary of `(U, B')` is a relative
coboundary of `(Y, U)`. -/
lemma coboundary_extendCochain_mem_relCoboundaries {B' : Set (TopCat.of U)} {p : ℕ}
    {ψ : Simplex (TopCat.of U) p → R} (hψ : ψ ∈ relCoboundaries R B' p) :
    coboundary R p (extendCochain ψ) ∈ relCoboundaries R U (p + 1) := by
  cases p with
  | zero =>
    rw [show ψ = 0 from (Submodule.mem_bot R).1 hψ, extendCochain_zero, map_zero]
    exact Submodule.zero_mem _
  | succ p =>
    obtain ⟨α, -, rfl⟩ := hψ
    refine ⟨extendCochain (coboundary R p α) - coboundary R p (extendCochain α),
      extendCochain_sub_mem_vanishing ?_, ?_⟩
    · rw [← coboundary_cochainPullback, cochainPullback_extendCochain]
    · rw [map_sub, coboundary_coboundary, sub_zero]

variable (R U)

/-- The coboundary `δ : H^p(U, B') → H^{p+1}(Y, U)` of the long exact sequence of the pair
`(Y, U)`: `δ [ψ]` is the class of `δ χ` for any cochain `χ` on `Y` extending `ψ`
(`relCohomologyDelta_mk`). -/
def relCohomologyDelta (B' : Set (TopCat.of U)) (p : ℕ) :
    relCohomology R B' p →ₗ[R] relCohomology R U (p + 1) :=
  Submodule.mapQ _ _ (relCocyclesDelta R U B' p) fun _ hψ ↦
    coboundary_extendCochain_mem_relCoboundaries hψ

variable {R U}

/-- `relCohomologyDelta` sends the class of a relative cocycle `ψ` to the class of
`relCocyclesDelta R U B' p ψ`. -/
lemma relCohomologyDelta_mk_eq {B' : Set (TopCat.of U)} {p : ℕ} (ψ : relCocycles R B' p) :
    relCohomologyDelta R U B' p (Submodule.Quotient.mk ψ) =
      Submodule.Quotient.mk (relCocyclesDelta R U B' p ψ) :=
  rfl

/-- **The coboundary on cochains.** For a relative cocycle `ψ` of `(U, B')` and any cochain `χ` of
`Y` with `χ|_U = ψ`, `δ [ψ] = [δ χ]` in `H^{p+1}(Y, U)`. -/
theorem relCohomologyDelta_mk {B' : Set (TopCat.of U)} {p : ℕ} (ψ : relCocycles R B' p)
    (χ : Simplex Y p → R) (hχ : cochainPullback R (subspaceInclusion Y U) p χ = ψ.1) :
    relCohomologyDelta R U B' p (Submodule.Quotient.mk ψ) =
      Submodule.Quotient.mk ⟨coboundary R p χ, coboundary_mem_relCocycles_of_cochainPullback (by
        rw [hχ]
        exact ((mem_relCocycles_iff R B' p _).1 ψ.2).2)⟩ := by
  refine (Submodule.Quotient.eq _).2 ?_
  change coboundary R p (extendCochain ψ.1) - coboundary R p χ ∈ relCoboundaries R U (p + 1)
  exact ⟨_, extendCochain_sub_mem_vanishing hχ, map_sub _ _ _⟩

/-- `relCohomologyForget` sends the class of a relative cocycle `φ` of `(Y, U)` to the class of
`φ` in `H^p(Y, B)`. -/
lemma relCohomologyForget_mk (hBU : B ⊆ U) {p : ℕ} (φ : relCocycles R U p) :
    relCohomologyForget R U hBU p (Submodule.Quotient.mk φ) =
      Submodule.Quotient.mk ⟨φ.1, cochainPullback_mem_relCocycles (𝟙 Y) hBU φ.2⟩ :=
  rfl

/-- `relCohomologyRestrict` sends the class of a relative cocycle `φ` of `(Y, B)` to the class of
its restriction to `U`. -/
lemma relCohomologyRestrict_mk {B' : Set (TopCat.of U)} (hB' : subspaceInclusion Y U ⁻¹' B = B')
    {p : ℕ} (φ : relCocycles R B p) :
    relCohomologyRestrict R U hB' p (Submodule.Quotient.mk φ) =
      Submodule.Quotient.mk ⟨cochainPullback R (subspaceInclusion Y U) p φ.1,
        cochainPullback_mem_relCocycles _ hB'.symm.subset φ.2⟩ :=
  rfl

/-- Exactness of `H^p(Y, U) → H^p(Y, B) → H^p(U, B')`. -/
theorem exact_relCohomologyForget_relCohomologyRestrict (hBU : B ⊆ U) {B' : Set (TopCat.of U)}
    (hB' : subspaceInclusion Y U ⁻¹' B = B') (p : ℕ) :
    Function.Exact (relCohomologyForget R U hBU p) (relCohomologyRestrict R U hB' p) := by
  subst hB'
  intro y
  constructor
  swap
  · rintro ⟨x, rfl⟩
    obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [relCohomologyForget_mk, relCohomologyRestrict_mk, Submodule.Quotient.mk_eq_zero]
    change cochainPullback R (subspaceInclusion Y U) p φ.1 ∈ relCoboundaries R _ p
    rw [(mem_vanishing_iff_cochainPullback_subspaceInclusion_eq_zero _).1
      ((mem_relCocycles_iff R U p _).1 φ.2).1]
    exact Submodule.zero_mem _
  obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [relCohomologyRestrict_mk, Submodule.Quotient.mk_eq_zero]
  intro h
  change cochainPullback R (subspaceInclusion Y U) p φ.1 ∈ relCoboundaries R _ p at h
  have hφ := (mem_relCocycles_iff R B p _).1 φ.2
  cases p with
  | zero =>
    exact ⟨Submodule.Quotient.mk ⟨φ.1, (mem_relCocycles_iff R U 0 _).2
      ⟨(mem_vanishing_iff_cochainPullback_subspaceInclusion_eq_zero _).2
        ((Submodule.mem_bot R).1 h), hφ.2⟩⟩, rfl⟩
  | succ p =>
    obtain ⟨α, hα, hαφ⟩ := h
    have hφ' : φ.1 - coboundary R p (extendCochain α) ∈ relCocycles R U (p + 1) := by
      refine (mem_relCocycles_iff R U (p + 1) _).2 ⟨?_, ?_⟩
      · rw [mem_vanishing_iff_cochainPullback_subspaceInclusion_eq_zero, map_sub,
          ← coboundary_cochainPullback, cochainPullback_extendCochain, hαφ, sub_self]
      · rw [map_sub, hφ.2, coboundary_coboundary, sub_zero]
    refine ⟨Submodule.Quotient.mk ⟨_, hφ'⟩, ?_⟩
    rw [relCohomologyForget_mk]
    refine (Submodule.Quotient.eq _).2 ?_
    change φ.1 - coboundary R p (extendCochain α) - φ.1 ∈ relCoboundaries R B (p + 1)
    rw [sub_sub_cancel_left, ← map_neg, ← extendCochain_neg]
    exact Submodule.mem_map_of_mem (extendCochain_mem_vanishing (Submodule.neg_mem _ hα))

/-- Exactness of `H^p(Y, B) → H^p(U, B') → H^{p+1}(Y, U)`. -/
theorem exact_relCohomologyRestrict_relCohomologyDelta {B' : Set (TopCat.of U)}
    (hB' : subspaceInclusion Y U ⁻¹' B = B') (hBU : B ⊆ U) (p : ℕ) :
    Function.Exact (relCohomologyRestrict R U hB' p) (relCohomologyDelta R U B' p) := by
  subst hB'
  intro y
  constructor
  swap
  · rintro ⟨x, rfl⟩
    obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [relCohomologyRestrict_mk, relCohomologyDelta_mk _ φ.1 rfl, Submodule.Quotient.mk_eq_zero]
    change coboundary R p φ.1 ∈ relCoboundaries R U (p + 1)
    rw [((mem_relCocycles_iff R B p _).1 φ.2).2]
    exact Submodule.zero_mem _
  obtain ⟨ψ, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [relCohomologyDelta_mk_eq, Submodule.Quotient.mk_eq_zero]
  intro h
  change coboundary R p (extendCochain ψ.1) ∈ relCoboundaries R U (p + 1) at h
  obtain ⟨χ, hχ, hχψ⟩ := h
  have hψ := (mem_relCocycles_iff R _ p _).1 ψ.2
  have hφ : extendCochain ψ.1 - χ ∈ relCocycles R B p := by
    refine (mem_relCocycles_iff R B p _).2 ⟨Submodule.sub_mem _
      (extendCochain_mem_vanishing hψ.1) (fun σ hσ ↦ hχ σ (hσ.trans hBU)), ?_⟩
    rw [map_sub, hχψ, sub_self]
  refine ⟨Submodule.Quotient.mk ⟨_, hφ⟩, ?_⟩
  rw [relCohomologyRestrict_mk]
  congr 1
  apply Subtype.ext
  change cochainPullback R (subspaceInclusion Y U) p (extendCochain ψ.1 - χ) = ψ.1
  rw [map_sub, cochainPullback_extendCochain,
    (mem_vanishing_iff_cochainPullback_subspaceInclusion_eq_zero _).1 hχ, sub_zero]

/-- Exactness of `H^p(U, B') → H^{p+1}(Y, U) → H^{p+1}(Y, B)`. -/
theorem exact_relCohomologyDelta_relCohomologyForget {B' : Set (TopCat.of U)}
    (hB' : subspaceInclusion Y U ⁻¹' B = B') (hBU : B ⊆ U) (p : ℕ) :
    Function.Exact (relCohomologyDelta R U B' p) (relCohomologyForget R U hBU (p + 1)) := by
  subst hB'
  intro y
  constructor
  swap
  · rintro ⟨x, rfl⟩
    obtain ⟨ψ, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [relCohomologyDelta_mk_eq, relCohomologyForget_mk, Submodule.Quotient.mk_eq_zero]
    change coboundary R p (extendCochain ψ.1) ∈ relCoboundaries R B (p + 1)
    exact Submodule.mem_map_of_mem
      (extendCochain_mem_vanishing ((mem_relCocycles_iff R _ p _).1 ψ.2).1)
  obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [relCohomologyForget_mk, Submodule.Quotient.mk_eq_zero]
  intro h
  change φ.1 ∈ relCoboundaries R B (p + 1) at h
  obtain ⟨α, hα, hαφ⟩ := h
  have hφ := (mem_relCocycles_iff R U (p + 1) _).1 φ.2
  have hψ : cochainPullback R (subspaceInclusion Y U) p α ∈
      relCocycles R (subspaceInclusion Y U ⁻¹' B) p := by
    refine (mem_relCocycles_iff R _ p _).2 ⟨cochainPullback_mem_vanishing _ subset_rfl hα, ?_⟩
    rw [coboundary_cochainPullback, hαφ]
    exact (mem_vanishing_iff_cochainPullback_subspaceInclusion_eq_zero _).1 hφ.1
  refine ⟨Submodule.Quotient.mk ⟨_, hψ⟩, ?_⟩
  rw [relCohomologyDelta_mk _ α rfl]
  congr 1
  exact Subtype.ext hαφ

/-- In degree `0` the forgetful map `H^0(Y, U) → H^0(Y, B)` is injective (there are no
coboundaries in degree `0`). -/
theorem injective_relCohomologyForget_zero (hBU : B ⊆ U) :
    Function.Injective (relCohomologyForget R U hBU 0) := by
  intro x y hxy
  obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨ψ, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [relCohomologyForget_mk, relCohomologyForget_mk, Submodule.Quotient.eq] at hxy
  refine (Submodule.Quotient.eq _).2 ?_
  change φ.1 - ψ.1 ∈ relCoboundaries R U 0
  rw [show φ.1 - ψ.1 = 0 from (Submodule.mem_bot R).1 hxy]
  exact Submodule.zero_mem _

end pair

end SingularCochain

end MMP
