module

public import MMP.AlgebraicGeometry.Chow.CapDegreeDivisorGysin

/-!
# Degrees against the Gysin map of a divisor, for one-dimensional caps on a threefold divisor

Let `f : W ⟶ Z` be a divisor (a regular closed immersion of codimension one) of complex schemes,
with `W` proper, and `H` an invertible module on `W`. This file computes
`deg(c₁(H|) ∩ f^!(t_*(c₁(L) ∩ [V])))` on `W ×_Z Z`, for `H|` the pull-back of `H`:

* for `t = f` (the self term, with `W` integral of dimension three), it is
  `deg(c₁(H) c₁(L) c₁(N') ∩ [W])` for any module `N'` isomorphic to the normal sheaf of `f`;
* for a closed subvariety `t : V ⟶ Z` of dimension three meeting `W` in a divisor
  `W ×_Z V ⟶ V`, and any invertible `K` on `W ×_Z Z` in place of `H|`, it is
  `deg(c₁(K|) c₁(L|) ∩ [W ×_Z V])`.

The invertibility hypotheses of the right-hand sides are instance arguments of the statements,
so that a caller's instance search supplies them. `MMP.Chow.capDegree_congr` passes between two
elaborations of one degree that differ only in these proofs.

## Main results

* `MMP.Chow.capDegree_congr`
* `MMP.Chow.capDegree_divisorGysin_pushforwardFirstChernCapFundamental_self`
* `MMP.Chow.capDegree_divisorGysin_pushforwardFirstChernCapFundamental_of_isRegular`
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Chow Stacks.AlgebraicGeometry.RegularIdealSheaf
  Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace MMP.Chow

attribute [local instance] fibreProductOver isOver_fibreProduct_fst isOver_fibreProduct_snd
  isComplexScheme_fibreProduct

/-- **Degrees of iterated caps only depend on the data.** Two applications of `capDegree` to equal
families and equal classes agree, whatever proofs of properness and invertibility they carry. -/
theorem capDegree_congr {k : Type u} [Field k] {X : Scheme.{u}} (q : X ⟶ Spec (.of k)) {d : ℕ}
    {L L' : Fin d → X.Modules} (hL : L = L') {p₁ p₂ : IsProper q}
    {h₁ : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)}
    {h₂ : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L' j)}
    {a b : chowGroup (fieldChowSituation k) q d} (hab : a = b) :
    @capDegree k _ X q p₁ d L h₁ a = @capDegree k _ X q p₂ d L' h₂ b := by
  subst hL hab
  rfl

/-- **The self term for a divisor of a threefold.** For a divisor `f : W ⟶ Z` with `W` proper of
dimension three, invertible modules `H`, `L` on `W` and a module `N'` isomorphic to the normal
sheaf `𝒞_{W/Z}^∨`: `deg(c₁(H|) ∩ f^!(f_*(c₁(L) ∩ [W]))) = deg(c₁(H) c₁(L) c₁(N') ∩ [W])`, for `H|`
the pull-back of `H` to `W ×_Z Z`. -/
theorem capDegree_divisorGysin_pushforwardFirstChernCapFundamental_self {W Z : Scheme.{0}}
    [W.Over (Spec (.of ℂ))] [Z.Over (Spec (.of ℂ))] (f : W ⟶ Z)
    [f.IsOver (Spec (.of ℂ))] [IsClosedImmersion f] [IsComplexScheme W]
    [IsComplexScheme Z] (hf : IsRegularClosedImmersionOfCodim f 1)
    [IsProper (W ↘ Spec (.of ℂ))] [IsIntegral W]
    (hW : topologicalKrullDim W = (1 + 1 + 1 : ℕ)) (H L N' : W.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible W.sheaf.obj W.ringCatSheaf.property L]
    [pq : IsProper (pullback.fst f (𝟙 Z) ≫ W ↘ Spec (.of ℂ))]
    [hK : ∀ j : Fin 1, SheafOfModules.IsInvertible (pullback f (𝟙 Z)).presheaf
      (pullback f (𝟙 Z)).ringCatSheaf.2
      ((fun _ : Fin 1 => (Scheme.Modules.pullback (pullback.fst f (𝟙 Z))).obj H) j)]
    [hS : ∀ j, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2
      ((Fin.snoc (Fin.snoc (fun _ : Fin 1 => H) L : Fin (1 + 1) → W.Modules) N' :
        Fin (1 + 1 + 1) → W.Modules) j)]
    (eN : Nonempty (dualSheaf (conormalModule f) ≅ N')) :
    @capDegree ℂ _ (pullback f (𝟙 Z)) (pullback.fst f (𝟙 Z) ≫ W ↘ Spec (.of ℂ)) pq 1
        (fun _ : Fin 1 => (Scheme.Modules.pullback (pullback.fst f (𝟙 Z))).obj H) hK
        (divisorGysin f hf 1 (pushforwardFirstChernCapFundamental f 1 L)) =
      capDegree ℂ (W ↘ Spec (.of ℂ))
        (Fin.snoc (Fin.snoc (fun _ : Fin 1 => H) L : Fin (1 + 1) → W.Modules) N' :
          Fin (1 + 1 + 1) → W.Modules)
        (fundamentalChowClass (fieldChowSituation ℂ) (W ↘ Spec (.of ℂ))
          ((1 + 1 + 1 : ℕ) : ℤ)) := by
  have hH : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 H := hS 0
  have hN : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 N' := hS (Fin.last _)
  have hv : pullback.lift (divisorFactor f f) f (divisorFactor_comp f f) ≫
      pullback.fst f (𝟙 Z) = 𝟙 _ := by
    rw [pullback.lift_fst, divisorFactor_self]
  exact (capDegree_congr _ rfl rfl).trans ((capDegree_divisorGysin_self f hf hW L N'
    (fun _ : Fin 1 => (Scheme.Modules.pullback (pullback.fst f (𝟙 Z))).obj H)
    (fun _ : Fin 1 => H) (hH := fun _ => hH)
    (fun _ => ⟨(Scheme.Modules.pullbackComp _ _).app H ≪≫
      (Scheme.Modules.pullbackCongr hv).app H ≪≫ (Scheme.Modules.pullbackId _).app H⟩) eN).trans
    (capDegree_congr _ rfl rfl))

/-- **The term of a transverse subvariety.** For a divisor `f : W ⟶ Z`, a closed subvariety
`t : V ⟶ Z` of dimension three whose intersection `W ×_Z V ⟶ V` with the divisor is again a
divisor, an invertible module `L` on `V` and a one-element family `K` of invertible modules on
`W ×_Z Z`:
`deg(c₁(K) ∩ f^!(t_*(c₁(L) ∩ [V]))) = deg(c₁(K|) c₁(L|) ∩ [W ×_Z V])`, for `K|` and `L|` the
pull-backs. -/
theorem capDegree_divisorGysin_pushforwardFirstChernCapFundamental_of_isRegular
    {W Z V : Scheme.{0}} [W.Over (Spec (.of ℂ))] [Z.Over (Spec (.of ℂ))]
    [V.Over (Spec (.of ℂ))] (f : W ⟶ Z) [f.IsOver (Spec (.of ℂ))]
    [IsClosedImmersion f] [IsComplexScheme W] [IsComplexScheme Z]
    (hf : IsRegularClosedImmersionOfCodim f 1) [IsProper (W ↘ Spec (.of ℂ))]
    [IsComplexScheme V] [IsIntegral V] (t : V ⟶ Z)
    [t.IsOver (Spec (.of ℂ))] [IsClosedImmersion t]
    (hV : topologicalKrullDim V = (1 + 1 + 1 : ℕ))
    (ht : IsRegularClosedImmersionOfCodim (pullback.snd f (t ≫ 𝟙 Z)) 1) (L : V.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property L]
    (K : Fin 1 → (pullback f (𝟙 Z)).Modules)
    [pq : IsProper (pullback.fst f (𝟙 Z) ≫ W ↘ Spec (.of ℂ))]
    [hK : ∀ j, SheafOfModules.IsInvertible (pullback f (𝟙 Z)).presheaf
      (pullback f (𝟙 Z)).ringCatSheaf.2 (K j)]
    [IsProper (pullback.fst f (t ≫ 𝟙 Z) ≫ W ↘ Spec (.of ℂ))]
    [∀ j, SheafOfModules.IsInvertible (pullback f (t ≫ 𝟙 Z)).presheaf
      (pullback f (t ≫ 𝟙 Z)).ringCatSheaf.2
      ((Fin.snoc (fun j => (Scheme.Modules.pullback (bivariantBaseChangeMap f (𝟙 Z) t)).obj (K j))
        ((Scheme.Modules.pullback (pullback.snd f (t ≫ 𝟙 Z))).obj L) :
          Fin (1 + 1) → (pullback f (t ≫ 𝟙 Z)).Modules) j)] :
    @capDegree ℂ _ (pullback f (𝟙 Z)) (pullback.fst f (𝟙 Z) ≫ W ↘ Spec (.of ℂ)) pq 1 K hK
        (divisorGysin f hf 1 (pushforwardFirstChernCapFundamental t 1 L)) =
      capDegree ℂ (pullback.fst f (t ≫ 𝟙 Z) ≫ W ↘ Spec (.of ℂ))
        (Fin.snoc (fun j => (Scheme.Modules.pullback (bivariantBaseChangeMap f (𝟙 Z) t)).obj (K j))
          ((Scheme.Modules.pullback (pullback.snd f (t ≫ 𝟙 Z))).obj L) :
            Fin (1 + 1) → (pullback f (t ≫ 𝟙 Z)).Modules)
        (fundamentalChowClass (fieldChowSituation ℂ)
          (pullback.fst f (t ≫ 𝟙 Z) ≫ W ↘ Spec (.of ℂ)) ((1 + 1 : ℕ) : ℤ)) :=
  (capDegree_congr _ rfl rfl).trans ((capDegree_divisorGysin_of_isRegular f hf t hV ht L K).trans
    (capDegree_congr _ rfl rfl))

end MMP.Chow
