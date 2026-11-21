import Atoms.Molecule.Construction.JoinAssociativity
import Atoms.Shape.Join
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.WithTerminal.Basic

open CategoryTheory MonoidalCategory Atoms.Molecule Atoms.Molecule.OGP

namespace Atoms.Shape

section Components

variable {U V : Atom}

def atomJoinFst (x : WithBot (atomJoin U V).ogp) : WithBot U.ogp :=
  joinBotFst (x.map (FiniteOGP.ofOGPIso (join U.ogp V.ogp)).inv)

def atomJoinSnd (x : WithBot (atomJoin U V).ogp) : WithBot V.ogp :=
  joinBotSnd (x.map (FiniteOGP.ofOGPIso (join U.ogp V.ogp)).inv)

def atomJoinPair (a : WithBot U.ogp) (b : WithBot V.ogp) : WithBot (atomJoin U V).ogp :=
  (joinPairBot U.ogp V.ogp a b).map (FiniteOGP.ofOGPIso (join U.ogp V.ogp)).hom

private theorem map_inv_map_hom {P Q : OGP.{0}} (e : P ≅ Q) (x : WithBot P) :
    (x.map e.hom).map e.inv = x := by
  induction x using WithBot.recBotCoe with
  | bot => rfl
  | coe a => exact congrArg WithBot.some (Iso.hom_inv_id_apply e a)

private theorem map_hom_map_inv {P Q : OGP.{0}} (e : P ≅ Q) (x : WithBot Q) :
    (x.map e.inv).map e.hom = x :=
  map_inv_map_hom e.symm x

@[simp] theorem atomJoinFst_atomJoinPair (a : WithBot U.ogp) (b : WithBot V.ogp) :
    atomJoinFst (atomJoinPair (V := V) a b) = a :=
  (congrArg joinBotFst (map_inv_map_hom _ _)).trans (joinBotFst_joinPairBot _ _)

@[simp] theorem atomJoinSnd_atomJoinPair (a : WithBot U.ogp) (b : WithBot V.ogp) :
    atomJoinSnd (atomJoinPair (U := U) a b) = b :=
  (congrArg joinBotSnd (map_inv_map_hom _ _)).trans (joinBotSnd_joinPairBot _ _)

@[simp] theorem atomJoinPair_atomJoinFst_atomJoinSnd (x : WithBot (atomJoin U V).ogp) :
    atomJoinPair (atomJoinFst x) (atomJoinSnd x) = x :=
  (congrArg (WithBot.map _) (joinPairBot_joinBotFst_joinBotSnd _)).trans (map_hom_map_inv _ x)

theorem atomJoinBot_ext {x y : WithBot (atomJoin U V).ogp}
    (hfst : atomJoinFst x = atomJoinFst y) (hsnd : atomJoinSnd x = atomJoinSnd y) : x = y := by
  rw [← atomJoinPair_atomJoinFst_atomJoinSnd x, ← atomJoinPair_atomJoinFst_atomJoinSnd y, hfst,
    hsnd]

variable {U' V' : Atom}

private theorem map_joinHom_map_inv (f : U ⟶ U') (g : V ⟶ V') (x : WithBot (atomJoin U V).ogp) :
    (x.map (joinHom f g)).map (FiniteOGP.ofOGPIso (join U'.ogp V'.ogp)).inv =
      (x.map (FiniteOGP.ofOGPIso (join U.ogp V.ogp)).inv).map (joinMap f g) := by
  induction x using WithBot.recBotCoe with
  | bot => rfl
  | coe a => exact congrArg WithBot.some (Iso.hom_inv_id_apply _ _)

@[simp] theorem atomJoinFst_map_joinHom (f : U ⟶ U') (g : V ⟶ V')
    (x : WithBot (atomJoin U V).ogp) :
    atomJoinFst (x.map (joinHom f g)) = (atomJoinFst x).map f :=
  (congrArg joinBotFst (map_joinHom_map_inv f g x)).trans (joinBotFst_map_joinMap _ _ _)

@[simp] theorem atomJoinSnd_map_joinHom (f : U ⟶ U') (g : V ⟶ V')
    (x : WithBot (atomJoin U V).ogp) :
    atomJoinSnd (x.map (joinHom f g)) = (atomJoinSnd x).map g :=
  (congrArg joinBotSnd (map_joinHom_map_inv f g x)).trans (joinBotSnd_map_joinMap _ _ _)

@[simp] theorem map_joinInclLeftHom (a : WithBot U.ogp) :
    a.map (joinInclLeftHom U V) = atomJoinPair a ⊥ := by
  induction a using WithBot.recBotCoe <;> rfl

@[simp] theorem map_joinInclRightHom (b : WithBot V.ogp) :
    b.map (joinInclRightHom U V) = atomJoinPair ⊥ b := by
  induction b using WithBot.recBotCoe <;> rfl

end Components

section ClosedJoin

variable {U V : Atom}

theorem atomJoin_le_iff {x y : (atomJoin U V).ogp} :
    x ≤ y ↔ atomJoinFst (x : WithBot (atomJoin U V).ogp) ≤
        atomJoinFst (y : WithBot (atomJoin U V).ogp) ∧
      atomJoinSnd (x : WithBot (atomJoin U V).ogp) ≤ atomJoinSnd (y : WithBot (atomJoin U V).ogp) :=
  (orderIsoOfIso (FiniteOGP.ofOGPIso (join U.ogp V.ogp))).symm.le_iff_le.symm.trans join_le_iff

theorem monotone_atomJoinFst : Monotone (atomJoinFst (U := U) (V := V)) := by
  intro x y h
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    induction y using WithBot.recBotCoe with
    | bot => exact absurd h (WithBot.not_coe_le_bot a)
    | coe b => exact (atomJoin_le_iff.1 (WithBot.coe_le_coe.1 h)).1

theorem monotone_atomJoinSnd : Monotone (atomJoinSnd (U := U) (V := V)) := by
  intro x y h
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    induction y using WithBot.recBotCoe with
    | bot => exact absurd h (WithBot.not_coe_le_bot a)
    | coe b => exact (atomJoin_le_iff.1 (WithBot.coe_le_coe.1 h)).2

private theorem forall_coe_eq_mem_of_le {P : Type*} [Preorder P] {A : LowerSet P}
    {o o' : WithBot P} (h : o' ≤ o) (ho : ∀ a : P, o = a → a ∈ A) : ∀ a : P, o' = a → a ∈ A := by
  rintro a rfl
  obtain ⟨b, hb, hab⟩ := WithBot.coe_le_iff.1 h
  exact A.lower hab (ho b hb)

def closedJoin (A : LowerSet U.ogp) (B : LowerSet V.ogp) : LowerSet (atomJoin U V).ogp where
  carrier := {x | (∀ a : U.ogp, atomJoinFst (x : WithBot (atomJoin U V).ogp) = a → a ∈ A) ∧
    ∀ b : V.ogp, atomJoinSnd (x : WithBot (atomJoin U V).ogp) = b → b ∈ B}
  lower' _ _ hyx hx :=
    ⟨forall_coe_eq_mem_of_le (monotone_atomJoinFst (WithBot.coe_le_coe.2 hyx)) hx.1,
      forall_coe_eq_mem_of_le (monotone_atomJoinSnd (WithBot.coe_le_coe.2 hyx)) hx.2⟩

theorem mem_closedJoin {A : LowerSet U.ogp} {B : LowerSet V.ogp}
    {x : (atomJoin U V).ogp} :
    x ∈ closedJoin A B ↔
      (∀ a : U.ogp, atomJoinFst (x : WithBot (atomJoin U V).ogp) = a → a ∈ A) ∧
        (∀ b : V.ogp, atomJoinSnd (x : WithBot (atomJoin U V).ogp) = b → b ∈ B) :=
  Iff.rfl

theorem closedJoin_mono {A A' : LowerSet U.ogp} {B B' : LowerSet V.ogp}
    (hA : A ≤ A') (hB : B ≤ B') : closedJoin A B ≤ closedJoin A' B' :=
  fun _ hx => ⟨fun a ha => hA (hx.1 a ha), fun b hb => hB (hx.2 b hb)⟩

theorem closedJoin_inf (A A' : LowerSet U.ogp) (B B' : LowerSet V.ogp) :
    closedJoin A B ⊓ closedJoin A' B' = closedJoin (A ⊓ A') (B ⊓ B') := by
  ext x
  simp only [SetLike.mem_coe, LowerSet.mem_inf_iff, mem_closedJoin]
  exact ⟨fun h => ⟨fun a ha => ⟨h.1.1 a ha, h.2.1 a ha⟩,
    fun b hb => ⟨h.1.2 b hb, h.2.2 b hb⟩⟩,
    fun h => ⟨⟨fun a ha => (h.1 a ha).1, fun b hb => (h.2 b hb).1⟩,
      ⟨fun a ha => (h.1 a ha).2, fun b hb => (h.2 b hb).2⟩⟩⟩

@[simp] theorem closedJoin_top_top : closedJoin (⊤ : LowerSet U.ogp) (⊤ : LowerSet V.ogp) = ⊤ :=
  top_unique fun _ _ => ⟨fun _ _ => LowerSet.mem_top, fun _ _ => LowerSet.mem_top⟩

private theorem le_coe_top (U : Atom) (a : WithBot U.ogp) : a ≤ (U.top : WithBot U.ogp) := by
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a => exact WithBot.coe_le_coe.2 (U.le_top a)

theorem coe_top_atomJoin (U V : Atom) :
    ((atomJoin U V).top : WithBot (atomJoin U V).ogp) =
      atomJoinPair (U.top : WithBot U.ogp) (V.top : WithBot V.ogp) := by
  obtain ⟨q, hq⟩ := WithBot.ne_bot_iff_exists.1 (fun h : atomJoinPair (U := U) (V := V)
    (U.top : WithBot U.ogp) (V.top : WithBot V.ogp) = ⊥ =>
      WithBot.coe_ne_bot ((atomJoinFst_atomJoinPair _ _).symm.trans (congrArg atomJoinFst h)))
  have hle : (atomJoin U V).top ≤ q := atomJoin_le_iff.2 (by
    rw [hq, atomJoinFst_atomJoinPair, atomJoinSnd_atomJoinPair]
    exact ⟨le_coe_top U _, le_coe_top V _⟩)
  rw [← hq, le_antisymm ((atomJoin U V).le_top q) hle]

theorem bdryFull_atomJoin (U V : Atom) :
    (atomJoin U V).ogp.bdryFull ⊤ =
      closedJoin (U.ogp.bdryFull ⊤) ⊤ ⊔ closedJoin ⊤ (V.ogp.bdryFull ⊤) := by
  have key : ∀ {P : Type} {o : WithBot P} {t : P}, (∀ a : P, o = a → a ≠ t) ↔ o ≠ t :=
    ⟨fun h e => h _ e rfl, fun h _ e ha => h (ha ▸ e)⟩
  ext x
  simp only [SetLike.mem_coe, LowerSet.mem_sup_iff, mem_closedJoin, Atom.mem_bdryFull_top_iff,
    LowerSet.mem_top, implies_true, and_true, true_and, key]
  rw [← not_and_or, ← WithBot.coe_inj.ne, coe_top_atomJoin]
  refine not_congr ⟨fun h => ⟨?_, ?_⟩, fun h => atomJoinBot_ext ?_ ?_⟩
  · rw [h, atomJoinFst_atomJoinPair]
  · rw [h, atomJoinSnd_atomJoinPair]
  · rw [h.1, atomJoinFst_atomJoinPair]
  · rw [h.2, atomJoinSnd_atomJoinPair]

end ClosedJoin

def atomJoinAssoc (U V W : Atom) : atomJoin (atomJoin U V) W ≅ atomJoin U (atomJoin V W) :=
  Atom.isoOfIso ((FiniteOGP.ofOGPIso (join (atomJoin U V).ogp W.ogp)).symm ≪≫
    join.mapIso (FiniteOGP.ofOGPIso (join U.ogp V.ogp)).symm (Iso.refl W.ogp) ≪≫
    joinAssoc U.ogp V.ogp W.ogp ≪≫
    join.mapIso (Iso.refl U.ogp) (FiniteOGP.ofOGPIso (join V.ogp W.ogp)) ≪≫
    FiniteOGP.ofOGPIso (join U.ogp (atomJoin V W).ogp))

section Associator

variable {U V W : Atom}

private theorem map_id_apply {P : OGP.{0}} (a : WithBot P) : a.map (𝟙 P) = a := by
  induction a using WithBot.recBotCoe <;> rfl

private theorem joinRightComponents_joinAssoc_conj (p : (atomJoin (atomJoin U V) W).ogp) :
    joinRightComponents U.ogp V.ogp W.ogp ((joinAssoc U.ogp V.ogp W.ogp).hom
      (joinMap (FiniteOGP.ofOGPIso (join U.ogp V.ogp)).inv (𝟙 W.ogp)
        ((FiniteOGP.ofOGPIso (join (atomJoin U V).ogp W.ogp)).inv p))) =
      (joinBotFst (((FiniteOGP.ofOGPIso (join (atomJoin U V).ogp W.ogp)).inv p).1.1.map
          (FiniteOGP.ofOGPIso (join U.ogp V.ogp)).inv),
        joinBotSnd (((FiniteOGP.ofOGPIso (join (atomJoin U V).ogp W.ogp)).inv p).1.1.map
          (FiniteOGP.ofOGPIso (join U.ogp V.ogp)).inv),
        ((FiniteOGP.ofOGPIso (join (atomJoin U V).ogp W.ogp)).inv p).1.2) :=
  (joinRightComponents_joinAssoc _ _ _ _).trans
    (congrArg (fun c => (_, _, c)) (map_id_apply _))

@[simp] theorem atomJoinFst_map_atomJoinAssoc (x : WithBot (atomJoin (atomJoin U V) W).ogp) :
    atomJoinFst (x.map (atomJoinAssoc U V W).hom) = atomJoinFst (atomJoinFst x) := by
  induction x using WithBot.recBotCoe with
  | bot => rfl
  | coe p =>
    exact (congrArg joinBotFst (congrArg WithBot.some (Iso.hom_inv_id_apply _ _))).trans
      ((map_id_apply _).trans (congrArg Prod.fst (joinRightComponents_joinAssoc_conj p)))

@[simp] theorem atomJoinFst_atomJoinSnd_map_atomJoinAssoc
    (x : WithBot (atomJoin (atomJoin U V) W).ogp) :
    atomJoinFst (atomJoinSnd (x.map (atomJoinAssoc U V W).hom)) = atomJoinSnd (atomJoinFst x) := by
  induction x using WithBot.recBotCoe with
  | bot => rfl
  | coe p =>
    exact (congrArg (fun y => atomJoinFst (joinBotSnd y))
      (congrArg WithBot.some (Iso.hom_inv_id_apply _ _))).trans
      ((congrArg joinBotFst (map_inv_map_hom _ _)).trans
        (congrArg (fun c => c.2.1) (joinRightComponents_joinAssoc_conj p)))

@[simp] theorem atomJoinSnd_atomJoinSnd_map_atomJoinAssoc
    (x : WithBot (atomJoin (atomJoin U V) W).ogp) :
    atomJoinSnd (atomJoinSnd (x.map (atomJoinAssoc U V W).hom)) = atomJoinSnd x := by
  induction x using WithBot.recBotCoe with
  | bot => rfl
  | coe p =>
    exact (congrArg (fun y => atomJoinSnd (joinBotSnd y))
      (congrArg WithBot.some (Iso.hom_inv_id_apply _ _))).trans
      ((congrArg joinBotSnd (map_inv_map_hom _ _)).trans
        (congrArg (fun c => c.2.2) (joinRightComponents_joinAssoc_conj p)))

private theorem map_comp_apply {U V W : Atom} (f : U ⟶ V) (g : V ⟶ W) (y : WithBot U.ogp) :
    y.map (f ≫ g) = (y.map f).map g := by
  induction y using WithBot.recBotCoe <;> rfl

@[reassoc] theorem atomJoinAssoc_hom_naturality {U U' V V' W W' : Atom}
    (f : U ⟶ U') (g : V ⟶ V') (h : W ⟶ W') :
    joinHom (joinHom f g) h ≫ (atomJoinAssoc U' V' W').hom =
      (atomJoinAssoc U V W).hom ≫ joinHom f (joinHom g h) := by
  refine Atom.hom_ext fun x => WithBot.coe_injective ?_
  have key : ((x : WithBot (atomJoin (atomJoin U V) W).ogp).map
      (joinHom (joinHom f g) h ≫ (atomJoinAssoc U' V' W').hom)) =
      (x : WithBot _).map ((atomJoinAssoc U V W).hom ≫ joinHom f (joinHom g h)) := by
    rw [map_comp_apply, map_comp_apply]
    refine atomJoinBot_ext ?_ (atomJoinBot_ext ?_ ?_) <;>
      simp only [atomJoinFst_map_atomJoinAssoc, atomJoinFst_atomJoinSnd_map_atomJoinAssoc,
        atomJoinSnd_atomJoinSnd_map_atomJoinAssoc, atomJoinFst_map_joinHom,
        atomJoinSnd_map_joinHom]
  exact key

end Associator

abbrev AugmentedAtom := WithInitial Atom

namespace AugmentedAtom

def tensorObj : AugmentedAtom → AugmentedAtom → AugmentedAtom
  | .of U, .of V => .of (atomJoin U V)
  | .star, X => X
  | X, .star => X

def tensorHom : {X₁ Y₁ X₂ Y₂ : AugmentedAtom} → (X₁ ⟶ Y₁) → (X₂ ⟶ Y₂) →
    (tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂)
  | .of _, .of _, .of _, .of _, f, g =>
    WithInitial.incl.map (joinHom (WithInitial.down f) (WithInitial.down g))
  | .of _, .of _, .star, .of _, f, _ =>
    WithInitial.incl.map (WithInitial.down f ≫ joinInclLeftHom _ _)
  | .star, .of _, .of _, .of _, _, g =>
    WithInitial.incl.map (WithInitial.down g ≫ joinInclRightHom _ _)
  | .star, .star, .of _, .of _, _, g => g
  | .of _, .of _, .star, .star, f, _ => f
  | .star, _, .star, _, _, _ => WithInitial.starInitial.to _

def associator : (X Y Z : AugmentedAtom) →
    tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z)
  | .of U, .of V, .of W => WithInitial.incl.mapIso (atomJoinAssoc U V W)
  | .star, .star, .star => Iso.refl _
  | .star, .of _, .star => Iso.refl _
  | .star, .star, .of _ => Iso.refl _
  | .star, .of _, .of _ => Iso.refl _
  | .of _, .star, .star => Iso.refl _
  | .of _, .star, .of _ => Iso.refl _
  | .of _, .of _, .star => Iso.refl _

def leftUnitor : (X : AugmentedAtom) → tensorObj .star X ≅ X
  | .of _ => Iso.refl _
  | .star => Iso.refl _

def rightUnitor : (X : AugmentedAtom) → tensorObj X .star ≅ X
  | .of _ => Iso.refl _
  | .star => Iso.refl _

end AugmentedAtom

instance : MonoidalCategoryStruct AugmentedAtom where
  tensorObj := AugmentedAtom.tensorObj
  tensorHom := AugmentedAtom.tensorHom
  whiskerLeft X _ _ f := AugmentedAtom.tensorHom (𝟙 X) f
  whiskerRight f Y := AugmentedAtom.tensorHom f (𝟙 Y)
  tensorUnit := WithInitial.star
  associator := AugmentedAtom.associator
  leftUnitor := AugmentedAtom.leftUnitor
  rightUnitor := AugmentedAtom.rightUnitor

@[simp] theorem tensorObj_of_of (U V : Atom) :
    (WithInitial.of U ⊗ WithInitial.of V : AugmentedAtom) = WithInitial.of (atomJoin U V) := rfl

@[simp] theorem tensorUnit_eq_star : (𝟙_ AugmentedAtom) = WithInitial.star := rfl

theorem associator_hom_of (U V W : Atom) :
    (α_ (WithInitial.of U) (WithInitial.of V) (WithInitial.of W) : _ ≅ (_ : AugmentedAtom)).hom =
      WithInitial.incl.map (atomJoinAssoc U V W).hom := rfl

def augmentedCarrier : AugmentedAtom ⥤ Type :=
  WithInitial.lift (Z := PUnit)
    { obj := fun U => WithBot U.ogp
      map := fun f => TypeCat.ofHom (WithBot.map f)
      map_id := fun _ => by
        ext y
        induction y using WithBot.recBotCoe <;> rfl
      map_comp := fun _ _ => by
        ext y
        induction y using WithBot.recBotCoe <;> rfl }
    (fun _ => TypeCat.ofHom fun _ => ⊥) (fun _ _ _ => rfl)

instance : augmentedCarrier.Faithful where
  map_injective {X Y} f g h :=
    match X, Y, f, g with
    | .of U, .of _, _, _ => Atom.hom_ext fun x =>
      WithBot.coe_injective (types_congr_hom h (x : WithBot U.ogp))
    | .star, _, _, _ => Subsingleton.elim _ _
    | .of _, .star, f, _ => (WithInitial.false_of_to_star f).elim

def augmentedCarrierμIso : (X Y : AugmentedAtom) →
    augmentedCarrier.obj X ⊗ augmentedCarrier.obj Y ≅ augmentedCarrier.obj (X ⊗ Y)
  | .of U, .of V =>
    { hom := TypeCat.ofHom fun p : WithBot U.ogp × WithBot V.ogp => atomJoinPair p.1 p.2
      inv := TypeCat.ofHom fun x : WithBot (atomJoin U V).ogp => (atomJoinFst x, atomJoinSnd x)
      hom_inv_id := by
        ext ⟨a, b⟩
        case h_fst => exact atomJoinFst_atomJoinPair (V := V) a b
        case h_snd => exact atomJoinSnd_atomJoinPair (U := U) a b
      inv_hom_id := by
        ext x
        exact atomJoinPair_atomJoinFst_atomJoinSnd x }
  | .star, _ => λ_ _
  | .of _, .star => ρ_ _

theorem augmentedCarrier_map_tensorHom :
    {X₁ Y₁ X₂ Y₂ : AugmentedAtom} → (f : X₁ ⟶ Y₁) → (g : X₂ ⟶ Y₂) →
    augmentedCarrier.map (f ⊗ₘ g) = (augmentedCarrierμIso _ _).inv ≫
      (augmentedCarrier.map f ⊗ₘ augmentedCarrier.map g) ≫ (augmentedCarrierμIso _ _).hom
  | .of _, .of _, .of _, .of _, f, g => by
    ext x
    exact (atomJoinPair_atomJoinFst_atomJoinSnd
      (x.map (joinHom (WithInitial.down f) (WithInitial.down g)))).symm.trans
      (congrArg₂ atomJoinPair (atomJoinFst_map_joinHom _ _ x) (atomJoinSnd_map_joinHom _ _ x))
  | .of _, .of _, .star, .of _, f, _ => by
    ext x
    exact (map_comp_apply _ _ x).trans (map_joinInclLeftHom _)
  | .star, .of _, .of _, .of _, _, g => by
    ext x
    exact (map_comp_apply _ _ x).trans (map_joinInclRightHom _)
  | .star, .star, .of _, .of _, _, _ => rfl
  | .of _, .of _, .star, .star, _, _ => rfl
  | .star, .of _, .star, .of _, _, _ => rfl
  | .star, .of _, .star, .star, _, _ => rfl
  | .star, .star, .star, .of _, _, _ => rfl
  | .star, .star, .star, .star, _, _ => rfl

private theorem map_atomJoinAssoc {U V W : Atom} (x : WithBot (atomJoin (atomJoin U V) W).ogp) :
    x.map (atomJoinAssoc U V W).hom = atomJoinPair (atomJoinFst (atomJoinFst x))
      (atomJoinPair (atomJoinSnd (atomJoinFst x)) (atomJoinSnd x)) :=
  atomJoinBot_ext ((atomJoinFst_map_atomJoinAssoc x).trans (atomJoinFst_atomJoinPair _ _).symm)
    (atomJoinBot_ext
      ((atomJoinFst_atomJoinSnd_map_atomJoinAssoc x).trans (by
        simp only [atomJoinSnd_atomJoinPair, atomJoinFst_atomJoinPair]))
      ((atomJoinSnd_atomJoinSnd_map_atomJoinAssoc x).trans (by
        simp only [atomJoinSnd_atomJoinPair])))

private theorem augmentedCarrier_map_associator : (X Y Z : AugmentedAtom) →
    augmentedCarrier.map (α_ X Y Z).hom =
      (((augmentedCarrierμIso _ _).symm ≪≫ ((augmentedCarrierμIso _ _).symm ⊗ᵢ .refl _))
        ≪≫ α_ (augmentedCarrier.obj X) (augmentedCarrier.obj Y) (augmentedCarrier.obj Z)
        ≪≫ ((.refl _ ⊗ᵢ augmentedCarrierμIso _ _) ≪≫ augmentedCarrierμIso _ _)).hom
  | .of U, .of V, .of W => by
    ext x
    exact map_atomJoinAssoc (U := U) (V := V) (W := W) x
  | .star, .star, .star => (augmentedCarrier.map_id _).trans (by ext; rfl)
  | .star, .of _, .star => (augmentedCarrier.map_id _).trans (by ext; rfl)
  | .star, .star, .of _ => (augmentedCarrier.map_id _).trans (by ext; rfl)
  | .star, .of _, .of _ => (augmentedCarrier.map_id _).trans (by
    ext x
    exact (atomJoinPair_atomJoinFst_atomJoinSnd x).symm)
  | .of _, .star, .star => (augmentedCarrier.map_id _).trans (by ext; rfl)
  | .of _, .star, .of _ => (augmentedCarrier.map_id _).trans (by
    ext x
    exact (atomJoinPair_atomJoinFst_atomJoinSnd x).symm)
  | .of _, .of _, .star => (augmentedCarrier.map_id _).trans (by
    ext x
    exact (atomJoinPair_atomJoinFst_atomJoinSnd x).symm)

instance : MonoidalCategory AugmentedAtom :=
  Monoidal.induced augmentedCarrier
    { μIso := augmentedCarrierμIso
      whiskerLeft_eq := fun X _ _ f => (augmentedCarrier_map_tensorHom (𝟙 X) f).trans
        (by rw [CategoryTheory.Functor.map_id, id_tensorHom])
      whiskerRight_eq := fun f Y => (augmentedCarrier_map_tensorHom f (𝟙 Y)).trans
        (by rw [CategoryTheory.Functor.map_id, tensorHom_id])
      tensorHom_eq := augmentedCarrier_map_tensorHom
      εIso := Iso.refl _
      associator_eq := augmentedCarrier_map_associator
      leftUnitor_eq := fun X => by
        cases X <;> exact (augmentedCarrier.map_id _).trans (by ext; rfl)
      rightUnitor_eq := fun X => by
        cases X <;> exact (augmentedCarrier.map_id _).trans (by ext; rfl) }

@[simp] theorem tensorHom_incl_map {U U' V V' : Atom} (f : U ⟶ U') (g : V ⟶ V') :
    (WithInitial.incl.map f ⊗ₘ WithInitial.incl.map g : _ ⟶ (_ : AugmentedAtom)) =
      WithInitial.incl.map (joinHom f g) := rfl

namespace AugmentedAtom

def inl (X Y : AugmentedAtom) : X ⟶ X ⊗ Y :=
  (ρ_ X).inv ≫ X ◁ WithInitial.starInitial.to Y

def inr (X Y : AugmentedAtom) : Y ⟶ X ⊗ Y :=
  (λ_ Y).inv ≫ WithInitial.starInitial.to X ▷ Y

theorem inl_of_of (U V : Atom) :
    inl (WithInitial.of U) (WithInitial.of V) = WithInitial.incl.map (joinInclLeftHom U V) :=
  (Category.id_comp _).trans
    (congrArg WithInitial.incl.map (Category.id_comp (joinInclLeftHom U V)))

theorem inr_of_of (U V : Atom) :
    inr (WithInitial.of U) (WithInitial.of V) = WithInitial.incl.map (joinInclRightHom U V) :=
  (Category.id_comp _).trans
    (congrArg WithInitial.incl.map (Category.id_comp (joinInclRightHom U V)))

@[reassoc] theorem inl_comp_tensorHom {X X' Y Y' : AugmentedAtom} (f : X ⟶ X') (g : Y ⟶ Y') :
    inl X Y ≫ (f ⊗ₘ g) = f ≫ inl X' Y' := by
  rw [inl, inl, Category.assoc, tensorHom_def, whisker_exchange_assoc, ← whiskerLeft_comp,
    WithInitial.starInitial.hom_ext (_ ≫ g) (WithInitial.starInitial.to Y'),
    rightUnitor_inv_naturality_assoc]

@[reassoc] theorem inr_comp_tensorHom {X X' Y Y' : AugmentedAtom} (f : X ⟶ X') (g : Y ⟶ Y') :
    inr X Y ≫ (f ⊗ₘ g) = g ≫ inr X' Y' := by
  rw [inr, inr, Category.assoc, tensorHom_def', ← whisker_exchange_assoc, ← comp_whiskerRight,
    WithInitial.starInitial.hom_ext (_ ≫ f) (WithInitial.starInitial.to X'),
    leftUnitor_inv_naturality_assoc]
  rfl

def closure (U : Atom) : WithBot U.ogp → AugmentedAtom :=
  WithBot.recBotCoe WithInitial.star fun x => WithInitial.of (Atom.ofClosure U x)

def closureIncl (U : Atom) : (a : WithBot U.ogp) → closure U a ⟶ WithInitial.of U :=
  WithBot.recBotCoe (WithInitial.starInitial.to _)
    fun x => WithInitial.incl.map (Atom.closureIncl U x)

theorem range_augmentedCarrier_map_closureIncl (U : Atom) (a : WithBot U.ogp) :
    Set.range (augmentedCarrier.map (closureIncl U a)) = (Set.Iic a : Set (WithBot U.ogp)) := by
  induction a using WithBot.recBotCoe with
  | bot =>
    refine Set.ext fun (c : WithBot U.ogp) => ?_
    refine ⟨?_, fun h => ⟨PUnit.unit, (le_bot_iff.1 (Set.mem_Iic.1 h)).symm⟩⟩
    rintro ⟨_, rfl⟩
    exact (le_rfl : (⊥ : WithBot U.ogp) ≤ ⊥)
  | coe x =>
    refine Set.ext fun (c : WithBot U.ogp) => ?_
    induction c using WithBot.recBotCoe with
    | bot =>
      exact iff_of_true ⟨(⊥ : WithBot (Atom.ofClosure U x).ogp), rfl⟩
        (bot_le : (⊥ : WithBot U.ogp) ≤ x)
    | coe y =>
      refine ⟨?_, fun h => ?_⟩
      · rintro ⟨z, hz⟩
        induction z using WithBot.recBotCoe with
        | bot => exact absurd hz WithBot.bot_ne_coe
        | coe z =>
          exact WithBot.coe_le_coe.2 (WithBot.coe_inj.1 hz ▸ closureIncl_mem_closure U x z)
      · obtain ⟨w, hw⟩ := (Atom.exists_closureIncl_eq_iff U x y).2 (WithBot.coe_le_coe.1 h)
        exact ⟨((w : (Atom.ofClosure U x).ogp) : WithBot _), congrArg WithBot.some hw⟩

theorem injective_augmentedCarrier_map_closureIncl (U : Atom) (a : WithBot U.ogp) :
    Function.Injective (augmentedCarrier.map (closureIncl U a)) := by
  induction a using WithBot.recBotCoe with
  | bot => exact fun _ _ _ => rfl
  | coe x => exact WithBot.map_injective (Atom.isInclusionHom_closureIncl U x)

theorem augmentedCarrier_map_tensorHom_apply {X Y : AugmentedAtom} {U V : Atom}
    (f : X ⟶ WithInitial.of U) (g : Y ⟶ WithInitial.of V) (z : augmentedCarrier.obj (X ⊗ Y)) :
    augmentedCarrier.map (f ⊗ₘ g) z =
      atomJoinPair (augmentedCarrier.map f ((augmentedCarrierμIso X Y).inv z).1)
        (augmentedCarrier.map g ((augmentedCarrierμIso X Y).inv z).2) := by
  rw [augmentedCarrier_map_tensorHom]
  rfl

theorem injective_augmentedCarrier_map_tensorHom {X Y : AugmentedAtom} {U V : Atom}
    {f : X ⟶ WithInitial.of U} {g : Y ⟶ WithInitial.of V}
    (hf : Function.Injective (augmentedCarrier.map f))
    (hg : Function.Injective (augmentedCarrier.map g)) :
    Function.Injective (augmentedCarrier.map (f ⊗ₘ g)) := by
  intro z z' e
  rw [augmentedCarrier_map_tensorHom_apply, augmentedCarrier_map_tensorHom_apply] at e
  have e₁ := hf ((atomJoinFst_atomJoinPair _ _).symm.trans
    ((congrArg atomJoinFst e).trans (atomJoinFst_atomJoinPair _ _)))
  have e₂ := hg ((atomJoinSnd_atomJoinPair _ _).symm.trans
    ((congrArg atomJoinSnd e).trans (atomJoinSnd_atomJoinPair _ _)))
  rw [← Iso.inv_hom_id_apply (augmentedCarrierμIso X Y) z,
    ← Iso.inv_hom_id_apply (augmentedCarrierμIso X Y) z', Prod.ext e₁ e₂]

instance mono_tensorHom_closureIncl (U V : Atom) (a : WithBot U.ogp) (b : WithBot V.ogp) :
    Mono (closureIncl U a ⊗ₘ closureIncl V b) :=
  augmentedCarrier.mono_of_mono_map ((mono_iff_injective _).2
    (injective_augmentedCarrier_map_tensorHom (injective_augmentedCarrier_map_closureIncl U a)
      (injective_augmentedCarrier_map_closureIncl V b)))

theorem exists_comp_eq_of_range_subset {X Z : AugmentedAtom} {W : Atom}
    (k : Z ⟶ WithInitial.of W) (hk : Function.Injective (augmentedCarrier.map k))
    (h : X ⟶ WithInitial.of W)
    (hh : Set.range (augmentedCarrier.map h) ⊆ Set.range (augmentedCarrier.map k)) :
    ∃ v : X ⟶ Z, v ≫ k = h := by
  cases X with
  | star => exact ⟨WithInitial.starInitial.to Z, WithInitial.starInitial.hom_ext _ _⟩
  | of T =>
    cases Z with
    | star =>
      obtain ⟨_, hz⟩ := hh ⟨(T.top : WithBot T.ogp), rfl⟩
      exact absurd hz WithBot.bot_ne_coe
    | of J =>
      have hk' : IsInclusionHom (WithInitial.down k) := fun a b hab =>
        WithBot.coe_injective (hk (a₁ := (a : WithBot J.ogp)) (a₂ := (b : WithBot J.ogp))
          (congrArg WithBot.some hab))
      obtain ⟨g, hg⟩ := exists_comp_eq_of_isInclusionHom (WithInitial.down k) hk'
        (WithInitial.down h) fun t => by
          obtain ⟨c, hc⟩ := hh ⟨(t : WithBot T.ogp), rfl⟩
          induction c using WithBot.recBotCoe with
          | bot => exact absurd hc WithBot.bot_ne_coe
          | coe c => exact ⟨c, WithBot.coe_injective hc⟩
      exact ⟨WithInitial.incl.map g,
        (WithInitial.incl.map_comp g _).symm.trans (congrArg WithInitial.incl.map hg)⟩

theorem exists_comp_closureIncl_eq {X : AugmentedAtom} {U : Atom} (h : X ⟶ WithInitial.of U) :
    ∃ (a : WithBot U.ogp) (p : X ⟶ closure U a),
      a ∈ Set.range (augmentedCarrier.map h) ∧ p ≫ closureIncl U a = h := by
  have key : ∃ a : WithBot U.ogp, a ∈ Set.range (augmentedCarrier.map h) ∧
      ∀ z, augmentedCarrier.map h z ∈ (Set.Iic a : Set (WithBot U.ogp)) := by
    cases X with
    | star =>
      exact ⟨augmentedCarrier.map h PUnit.unit, ⟨_, rfl⟩, fun _ => @le_rfl (WithBot U.ogp) _ _⟩
    | of T =>
      refine ⟨((WithInitial.down h T.top : U.ogp) : WithBot U.ogp), ⟨(T.top : WithBot T.ogp), rfl⟩,
        fun z => ?_⟩
      induction z using WithBot.recBotCoe with
      | bot => exact (bot_le : (⊥ : WithBot U.ogp) ≤ _)
      | coe t =>
        exact WithBot.coe_le_coe.2
          (LowerSet.mem_Iic_iff.1 (apply_mem_closure_apply_top (WithInitial.down h) t))
  obtain ⟨a, ha, hle⟩ := key
  obtain ⟨p, hp⟩ := exists_comp_eq_of_range_subset (closureIncl U a)
    (injective_augmentedCarrier_map_closureIncl U a) h (by
      rw [range_augmentedCarrier_map_closureIncl]
      rintro _ ⟨z, rfl⟩
      exact hle z)
  exact ⟨a, p, ha, hp⟩

theorem exists_comp_tensorHom_closureIncl_eq {T U V : Atom} (f : T ⟶ atomJoin U V)
    {a : WithBot U.ogp} {b : WithBot V.ogp}
    (ha : atomJoinFst (f T.top : WithBot (atomJoin U V).ogp) ≤ a)
    (hb : atomJoinSnd (f T.top : WithBot (atomJoin U V).ogp) ≤ b) :
    ∃ v : WithInitial.of T ⟶ closure U a ⊗ closure V b,
      v ≫ (closureIncl U a ⊗ₘ closureIncl V b) = WithInitial.incl.map f := by
  refine exists_comp_eq_of_range_subset _ (injective_augmentedCarrier_map_tensorHom
    (injective_augmentedCarrier_map_closureIncl U a)
    (injective_augmentedCarrier_map_closureIncl V b)) _ ?_
  rintro _ ⟨z, rfl⟩
  have hz : (z.map f : WithBot (atomJoin U V).ogp) ≤ (f T.top : WithBot (atomJoin U V).ogp) := by
    induction z using WithBot.recBotCoe with
    | bot => exact (bot_le : (⊥ : WithBot (atomJoin U V).ogp) ≤ _)
    | coe t =>
      exact WithBot.coe_le_coe.2 (LowerSet.mem_Iic_iff.1 (apply_mem_closure_apply_top f t))
  obtain ⟨z₁, hz₁⟩ :
      atomJoinFst (z.map f) ∈ Set.range (augmentedCarrier.map (closureIncl U a)) := by
    rw [range_augmentedCarrier_map_closureIncl]
    exact (monotone_atomJoinFst hz).trans ha
  obtain ⟨z₂, hz₂⟩ :
      atomJoinSnd (z.map f) ∈ Set.range (augmentedCarrier.map (closureIncl V b)) := by
    rw [range_augmentedCarrier_map_closureIncl]
    exact (monotone_atomJoinSnd hz).trans hb
  refine ⟨(augmentedCarrierμIso _ _).hom (z₁, z₂), ?_⟩
  refine (augmentedCarrier_map_tensorHom_apply _ _ _).trans ?_
  rw [Iso.hom_inv_id_apply, hz₁, hz₂, atomJoinPair_atomJoinFst_atomJoinSnd]
  rfl

end AugmentedAtom

end Atoms.Shape
