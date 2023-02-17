Aux.vo Aux.glob Aux.v.beautified Aux.required_vo: Aux.v Syntax.vo
Aux.vio: Aux.v Syntax.vio
Aux.vos Aux.vok Aux.required_vos: Aux.v Syntax.vos
Syntax.vo Syntax.glob Syntax.v.beautified Syntax.required_vo: Syntax.v 
Syntax.vio: Syntax.v 
Syntax.vos Syntax.vok Syntax.required_vos: Syntax.v 
SemanticsTypes.vo SemanticsTypes.glob SemanticsTypes.v.beautified SemanticsTypes.required_vo: SemanticsTypes.v Aux.vo Syntax.vo
SemanticsTypes.vio: SemanticsTypes.v Aux.vio Syntax.vio
SemanticsTypes.vos SemanticsTypes.vok SemanticsTypes.required_vos: SemanticsTypes.v Aux.vos Syntax.vos
SemanticsAux.vo SemanticsAux.glob SemanticsAux.v.beautified SemanticsAux.required_vo: SemanticsAux.v Aux.vo Syntax.vo SemanticsTypes.vo
SemanticsAux.vio: SemanticsAux.v Aux.vio Syntax.vio SemanticsTypes.vio
SemanticsAux.vos SemanticsAux.vok SemanticsAux.required_vos: SemanticsAux.v Aux.vos Syntax.vos SemanticsTypes.vos
Semantics.vo Semantics.glob Semantics.v.beautified Semantics.required_vo: Semantics.v Syntax.vo SemanticsTypes.vo SemanticsAux.vo
Semantics.vio: Semantics.v Syntax.vio SemanticsTypes.vio SemanticsAux.vio
Semantics.vos Semantics.vok Semantics.required_vos: Semantics.v Syntax.vos SemanticsTypes.vos SemanticsAux.vos
Interp.vo Interp.glob Interp.v.beautified Interp.required_vo: Interp.v Syntax.vo SemanticsTypes.vo SemanticsAux.vo
Interp.vio: Interp.v Syntax.vio SemanticsTypes.vio SemanticsAux.vio
Interp.vos Interp.vok Interp.required_vos: Interp.v Syntax.vos SemanticsTypes.vos SemanticsAux.vos
Prettyprint.vo Prettyprint.glob Prettyprint.v.beautified Prettyprint.required_vo: Prettyprint.v Aux.vo Syntax.vo SemanticsTypes.vo
Prettyprint.vio: Prettyprint.v Aux.vio Syntax.vio SemanticsTypes.vio
Prettyprint.vos Prettyprint.vok Prettyprint.required_vos: Prettyprint.v Aux.vos Syntax.vos SemanticsTypes.vos
Parse.vo Parse.glob Parse.v.beautified Parse.required_vo: Parse.v Syntax.vo
Parse.vio: Parse.v Syntax.vio
Parse.vos Parse.vok Parse.required_vos: Parse.v Syntax.vos
Extraction.vo Extraction.glob Extraction.v.beautified Extraction.required_vo: Extraction.v Syntax.vo Interp.vo
Extraction.vio: Extraction.v Syntax.vio Interp.vio
Extraction.vos Extraction.vok Extraction.required_vos: Extraction.v Syntax.vos Interp.vos
