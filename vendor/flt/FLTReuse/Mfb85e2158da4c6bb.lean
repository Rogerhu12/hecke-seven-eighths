module

public import FLTReuse.Mbfe19ea9534a55ec
public import FLTReuse.M1868db956c866c8d

@[expose] public section

namespace P2MW.S_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar

open NumberField NumberField.StandardAddChar AutomorphicForm

theorem solution
    (F : Type) [Field F] [NumberField F] :
    IsGlobalAddChar F (stdAddChar F) :=
  (adelicTraceData F).isGlobalAddChar_psiK
