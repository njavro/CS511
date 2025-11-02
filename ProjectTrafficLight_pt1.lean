import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary
namespace TrafficLight2FSM

structure Context where
  dummy : Unit := ()
inductive TLState (ctx : Context) where
  | nsGreen_ewRed
  | nsYellow_ewRed
  | nsRed_ewGreen
  | nsRed_ewYellow
deriving DecidableEq, Repr

@[simp]
def TLState.invariant (_ : TLState ctx) : Prop := True

instance : Machine Context (TLState ctx) where
  context   := ctx
  invariant := TLState.invariant
  default   := .nsGreen_ewRed

def NS_ToYellow : OrdinaryEvent (TLState ctx) Unit Unit := newEvent'' {
  guard  := fun s => s = .nsGreen_ewRed
  action := fun _ _ => .nsYellow_ewRed
  safety := fun _ => by simp [Machine.invariant]
}

def SwitchToEW : OrdinaryEvent (TLState ctx) Unit Unit := newEvent'' {
  guard  := fun s => s =.nsYellow_ewRed
  action := fun _ _ =>.nsRed_ewGreen
  safety := fun _ => by simp [Machine.invariant]
}

def EW_ToYellow : OrdinaryEvent (TLState ctx) Unit Unit := newEvent'' {
  guard  :=fun s => s = .nsRed_ewGreen
  action :=fun _ _ => .nsRed_ewYellow
  safety :=fun _ => by simp [Machine.invariant]
}

def SwitchToNS : OrdinaryEvent (TLState ctx) Unit Unit := newEvent'' {
  guard  :=fun s => s =.nsRed_ewYellow
  action :=fun _ _ =>.nsGreen_ewRed
  safety :=fun _ => by simp [Machine.invariant]
}

theorem deadlockFreedom (s : TLState ctx) :
  Machine.invariant s →
  NS_ToYellow.guard s () ∨ SwitchToEW.guard s () ∨
  EW_ToYellow.guard s () ∨ SwitchToNS.guard s () := by
  intro _
  cases s <;> simp [NS_ToYellow, SwitchToEW, EW_ToYellow, SwitchToNS, newEvent'']

end TrafficLight2FSM
