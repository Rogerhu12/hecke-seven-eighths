module

public import FLTReuse.Mbfe19ea9534a55ec
public import FLTReuse.M1868db956c866c8d
public import FLTReuse.Mfb85e2158da4c6bb

@[expose] public section

open NumberField NumberField.StandardAddChar AutomorphicForm
theorem NumberField.StandardAddChar.isGlobalAddChar_stdAddChar
    (F : Type) [Field F] [NumberField F] :
    IsGlobalAddChar F (stdAddChar F) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar.solution
