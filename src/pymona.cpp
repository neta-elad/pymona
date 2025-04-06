#include <string_view>
#include <utility>
#include <variant>
#include <format>
#include <concepts>

#include <nanobind/nanobind.h>
#include <nanobind/stl/string.h>
#include <nanobind/stl/string_view.h>
#include <nanobind/stl/variant.h>
#include <nanobind/stl/map.h>
#include <nanobind/stl/set.h>
#include <nanobind/stl/optional.h>

#include "symboltable.h"
#include "printline.h"
#include "dfa.h"
#include "env.h"
#include "lib.h"
#include "offsets.h"
#include "predlib.h"
#include "untyped.h"

extern "C" {
#include "mem.h"
}

#include "ident.h"

#include "model.h"
#include "utils.h"

Options options;
MonaUntypedAST *untypedAST;
SymbolTable symbolTable(1019);
PredicateLib predicateLib;
Offsets offsets;
CodeTable *codeTable;
Guide guide;
AutLib lib;
int numTypes = 0;
bool regenerate = false;

namespace nb = nanobind;
using namespace nb::literals;

using Identifiers = std::set<Ident>;

Identifiers identUnion(const Identifiers &i1, const Identifiers &i2) {
    Identifiers result(i1);
    result.insert(i2.begin(), i2.end());
    return std::move(result);
}

struct IdentContainer {
    Ident ident;
};

template<typename T>
    requires std::derived_from<T, AST>
struct AstRef {
    Identifiers identifiers;
    std::shared_ptr<T> ast;
};

struct BoolRef : AstRef<ASTForm> {
};

struct BoolIdent : BoolRef, IdentContainer {
    explicit BoolIdent(Ident ident)
        : BoolRef{
              Identifiers{ident},
              std::make_shared<ASTForm_Var0>(ident)
          }, IdentContainer{ident} {
    }

    explicit BoolIdent(std::string_view name)
        : BoolIdent(addVar(name, Varname0)) {
    }
};

struct ElementRef : AstRef<ASTTerm1> {
    ElementRef(int i)
        : ElementRef(Identifiers{}, std::make_shared<ASTTerm1_Int>(i)) {
    }

    ElementRef(Identifiers identifiers, ASTTerm1Ptr ast)
        : AstRef(std::move(identifiers), std::move(ast)) {
    }
};

struct ElementInt : ElementRef {
    ElementInt(int ii) : ElementRef(ii), i(ii) {
    }

    int i;
};

struct ElementIdent : ElementRef, IdentContainer {
    explicit ElementIdent(Ident ident)
        : ElementRef{
              Identifiers{ident},
              std::make_shared<ASTTerm1_Var1>(ident)
          }, IdentContainer{ident} {
    }

    explicit ElementIdent(std::string_view name)
        : ElementIdent(addVar(name, Varname1)) {
    }
};

struct SetRef : AstRef<ASTTerm2> {
};

struct SetIdent : SetRef, IdentContainer {
    explicit SetIdent(Ident ident)
        : SetRef{
              Identifiers{ident},
              std::make_shared<ASTTerm2_Var2>(ident)
          }, IdentContainer{ident} {
    }

    explicit SetIdent(std::string_view name)
        : SetIdent(addVar(name, Varname2)) {
    }
};

ElementInt makeInt(int i) {
    return i;
}

template<typename T>
    requires std::derived_from<T, ASTForm_tt>
BoolRef makeElementElementFormula(const ElementRef &e1, const ElementRef &e2) {
    return BoolRef{
        identUnion(e1.identifiers, e2.identifiers),
        std::make_shared<T>(e1.ast, e2.ast)
    };
}

BoolRef makeGreaterThan(const ElementRef &i1, const ElementRef &i2) {
    return makeElementElementFormula<ASTForm_Less>(i2, i1);
}

BoolRef makeGeq(const ElementRef &i1, const ElementRef &i2) {
    return makeElementElementFormula<ASTForm_LessEq>(i2, i1);
}

BoolRef makeSub(const SetRef &s1, const SetRef &s2) {
    return BoolRef{
        identUnion(s1.identifiers, s2.identifiers),
        std::make_shared<ASTForm_Sub>(s1.ast, s2.ast)
    };
}

BoolRef makeSup(const SetRef &s1, const SetRef &s2) {
    return makeSub(s2, s1);
}

BoolRef makeIn(const ElementRef &e, const SetRef &s) {
    return BoolRef{
        identUnion(e.identifiers, s.identifiers),
        std::make_shared<ASTForm_In>(e.ast, s.ast)
    };
}

BoolRef makeNi(const SetRef &s, const ElementRef &e) {
    return makeIn(e, s);
}

BoolRef makeTrue() {
    return BoolRef{
        Identifiers{},
        std::make_shared<ASTForm_True>()
    };
}

BoolRef makeFalse() {
    return BoolRef{
        Identifiers{},
        std::make_shared<ASTForm_False>()
    };
}

SetRef makeEmpty() {
    return SetRef{
        Identifiers{},
        std::make_shared<ASTTerm2_Empty>()
    };
}

BoolRef makeIsEmpty(const SetRef &s) {
    return BoolRef{
        s.identifiers,
        std::make_shared<ASTForm_EmptyPred>(s.ast)
    };
}

BoolRef makeAnd(nb::args args) {
    Identifiers identifiers;
    ASTFormPtr result = std::make_shared<ASTForm_True>();
    for (auto arg: args) {
        BoolRef f = nb::cast<BoolRef>(arg);
        identifiers.insert(f.identifiers.begin(), f.identifiers.end());
        result = std::make_shared<ASTForm_And>(
            std::move(result), f.ast
        );
    }
    return BoolRef{identifiers, std::move(result)};
}

BoolRef makeOr(nb::args args) {
    Identifiers identifiers;
    ASTFormPtr result = std::make_shared<ASTForm_False>();
    for (auto arg: args) {
        BoolRef f = nb::cast<BoolRef>(arg);
        identifiers.insert(f.identifiers.begin(), f.identifiers.end());
        result = std::make_shared<ASTForm_Or>(
            std::move(result), f.ast
        );
    }
    return BoolRef{identifiers, std::move(result)};
}

BoolRef makeImplies(const BoolRef &f1, const BoolRef &f2) {
    return BoolRef{
        identUnion(f1.identifiers, f2.identifiers),
        std::make_shared<ASTForm_Impl>(f1.ast, f2.ast)
    };
}

BoolRef makeIff(const BoolRef &f1, const BoolRef &f2) {
    return BoolRef{
        identUnion(f1.identifiers, f2.identifiers),
        std::make_shared<ASTForm_Biimpl>(f1.ast, f2.ast)
    };
}

BoolRef makeNot(const BoolRef &f) {
    return BoolRef{
        f.identifiers,
        std::make_shared<ASTForm_Not>(f.ast)
    };
}

BoolRef makeNiff(const BoolRef &f1, const BoolRef &f2) {
    return makeNot(makeIff(f1, f2));
}

BoolRef makeSetEq(const SetRef &s1, const SetRef &s2) {
    return BoolRef{
        identUnion(s1.identifiers, s2.identifiers),
        std::make_shared<ASTForm_Equal2>(s1.ast, s2.ast)
    };
}

BoolRef makeSetNeq(const SetRef &s1, const SetRef &s2) {
    return BoolRef{
        identUnion(s1.identifiers, s2.identifiers),
        std::make_shared<ASTForm_NotEqual2>(s1.ast, s2.ast)
    };
}

BoolRef makeForall1(const ElementIdent &id, const BoolRef &f) {
    IdentList *list = new IdentList(id.ident);
    return BoolRef{
        identUnion(id.identifiers, f.identifiers),
        std::make_shared<ASTForm_All1>(nullptr, list, f.ast)
    };
}

BoolRef makeForall1Iter(
    nb::typed<nb::iterable, ElementIdent> ids,
    const BoolRef &f
) {
    IdentList *list = new IdentList;
    Identifiers identifiers;
    for (auto id: nb::iter(ids)) {
        Ident ident = nb::cast<ElementIdent>(id).ident;
        identifiers.insert(ident);
        list->insert(ident);
    }
    identifiers.insert(f.identifiers.begin(), f.identifiers.end());
    return BoolRef{
        identifiers,
        std::make_shared<ASTForm_All1>(nullptr, list, f.ast)
    };
}

BoolRef makeExists1(const ElementIdent &id, const BoolRef &f) {
    IdentList *list = new IdentList(id.ident);
    return BoolRef{
        identUnion(id.identifiers, f.identifiers),
        std::make_shared<ASTForm_Ex1>(nullptr, list, f.ast)
    };
}

BoolRef makeExists1Iter(
    nb::typed<nb::iterable, ElementIdent> ids,
    const BoolRef &f
) {
    IdentList *list = new IdentList;
    Identifiers identifiers;
    for (auto id: nb::iter(ids)) {
        Ident ident = nb::cast<ElementIdent>(id).ident;
        identifiers.insert(ident);
        list->insert(ident);
    }
    identifiers.insert(f.identifiers.begin(), f.identifiers.end());
    return BoolRef{
        identifiers,
        std::make_shared<ASTForm_Ex1>(nullptr, list, f.ast)
    };
}

BoolRef makeForall2(const SetIdent &id, const BoolRef &f) {
    IdentList *list = new IdentList(id.ident);
    return BoolRef{
        identUnion(id.identifiers, f.identifiers),
        std::make_shared<ASTForm_All2>(nullptr, list, f.ast)
    };
}

BoolRef makeForall2Iter(
    nb::typed<nb::iterable, SetIdent> ids,
    const BoolRef &f
) {
    IdentList *list = new IdentList;
    Identifiers identifiers;
    for (auto id: nb::iter(ids)) {
        Ident ident = nb::cast<SetIdent>(id).ident;
        identifiers.insert(ident);
        list->insert(ident);
    }
    identifiers.insert(f.identifiers.begin(), f.identifiers.end());
    return BoolRef{
        identifiers,
        std::make_shared<ASTForm_All2>(nullptr, list, f.ast)
    };
}

BoolRef makeExists2(const SetIdent &id, const BoolRef &f) {
    IdentList *list = new IdentList(id.ident);
    return BoolRef{
        identUnion(id.identifiers, f.identifiers),
        std::make_shared<ASTForm_Ex2>(nullptr, list, f.ast)
    };
}

BoolRef makeExists2Iter(
    nb::typed<nb::iterable, SetIdent> ids,
    const BoolRef &f
) {
    IdentList *list = new IdentList;
    Identifiers identifiers;
    for (auto id: nb::iter(ids)) {
        Ident ident = nb::cast<SetIdent>(id).ident;
        identifiers.insert(ident);
        list->insert(ident);
    }
    identifiers.insert(f.identifiers.begin(), f.identifiers.end());
    return BoolRef{
        identifiers,
        std::make_shared<ASTForm_Ex2>(nullptr, list, f.ast)
    };
}

std::optional<Model> solve(const BoolRef &formula) {
    MonaAST ast{formula.ast};
    for (const auto ident: formula.identifiers) {
        ast.globals.insert(ident);
    }
    return getModel(ast);
}

template<typename T>
    requires std::derived_from<T, IdentContainer>
std::string_view lookupSymbol(const T &container) {
    return symbolTable.lookupSymbol(container.ident);
}

struct PredRef : IdentContainer {
    int n;
};

PredRef doMakePred(
    std::string_view name,
    nb::typed<nb::iterable, std::variant<BoolIdent, ElementIdent, SetIdent> > ids,
    const BoolRef &f,
    bool macro
) {
    IdentList *list = new IdentList;
    for (auto id: nb::iter(ids)) {
        Ident ident = nb::cast<IdentContainer>(id).ident;
        list->insert(ident);
    }

    int n = list->size();

    Ident pred = addPredicate(name);

    IdentList *bound = list->copy(), *frees = new IdentList;
    f.ast->freeVars(frees, bound);

    predicateLib.insert(
        list,
        frees,
        bound,
        f.ast,
        true,
        pred
    );

    return PredRef{pred, n};
}

PredRef makePred(
    std::string_view name,
    nb::typed<nb::iterable, std::variant<BoolIdent, ElementIdent, SetIdent> > ids,
    const BoolRef &f) {
    return doMakePred(name, ids, f, false);
}

PredRef makeMacro(
    std::string_view name,
    nb::typed<nb::iterable, std::variant<BoolIdent, ElementIdent, SetIdent> > ids,
    const BoolRef &f) {
    return doMakePred(name, ids, f, true);
}

BoolRef makePredCall(const PredRef &pred, nb::args args) {
    Identifiers identifiers;
    SharedASTList salist;
    for (auto i = 0; i < args.size(); ++i) {
        auto arg = args[i];
        if (nb::isinstance<BoolRef>(arg)) {
            const auto &ref = nb::cast<const BoolRef &>(arg);
            identifiers.insert(ref.identifiers.begin(), ref.identifiers.end());
            salist.push_back(ref.ast);
        } else if (nb::isinstance<int>(arg)) {
            int n = nb::cast<int>(arg);
            salist.push_back(std::make_shared<ASTTerm1_Int>(n));
        } else if (nb::isinstance<ElementRef>(arg)) {
            const auto &ref = nb::cast<const ElementRef &>(arg);
            identifiers.insert(ref.identifiers.begin(), ref.identifiers.end());
            salist.push_back(ref.ast);
        } else if (nb::isinstance<SetRef>(arg)) {
            const auto &ref = nb::cast<const SetRef &>(arg);
            identifiers.insert(ref.identifiers.begin(), ref.identifiers.end());
            salist.push_back(ref.ast);
        } else {
            throw nanobind::value_error(std::format(
                "Bad argument passed to predicate at {}: {}",
                i,
                nb::repr(arg).c_str()
            ).c_str());
        }
    }

    Ident id = pred.ident;
    int badArg;

    auto alist = salist.toAstList();

    switch (predicateLib.testTypes(id, alist.get(), &badArg, true)) {
        case tWrongParameterType:
            alist->reset();
            throw nb::value_error(std::format(
                "Wrong type of parameter {} to {}",
                badArg,
                symbolTable.lookupSymbol(id)
            ).c_str());

        case tWrongNoParameters:
            alist->reset();
            throw nb::value_error(std::format(
                "Wrong number of parameters to {}, expected {}, got {}",
                symbolTable.lookupSymbol(id),
                pred.n,
                salist.size()
            ).c_str());
        case tOK:
            ;
    }
    alist->reset();

    return BoolRef{
        std::move(identifiers),
        std::make_shared<ASTForm_Call>(
            id, salist)
    };
}

ElementRef makePlusRightInt(const ElementRef &i1, const ElementInt &i2) {
    return ElementRef{
        i1.identifiers,
        std::make_shared<ASTTerm1_Plus>(i1.ast, i2.i)
    };
}

ElementRef makePlusLeftInt(const ElementInt &i1, const ElementRef &i2) {
    return ElementRef{
        i2.identifiers,
        std::make_shared<ASTTerm1_Plus>(i2.ast, i1.i)
    };
}

ElementRef makeMinus(const ElementRef &i1, const ElementInt &i2) {
    return ElementRef{
        i1.identifiers,
        std::make_shared<ASTTerm1_Minus>(i1.ast, i2.i)
    };
}

SetRef makeSet(const nb::args &args) {
    Identifiers identifiers;
    SharedASTList elements;
    for (auto arg: args) {
        ElementRef f = nb::cast<ElementRef>(arg);
        identifiers.insert(f.identifiers.begin(), f.identifiers.end());
        elements.push_back(f.ast);
    }
    return SetRef{
        identifiers,
        std::make_shared<ASTTerm2_Set>(elements)
    };
}

ElementRef makeMinArgs(const nb::args &args) {
    Identifiers identifiers;
    SharedASTList elements;
    for (auto arg: args) {
        ElementRef f = nb::cast<ElementRef>(arg);
        identifiers.insert(f.identifiers.begin(), f.identifiers.end());
        elements.push_back(f.ast);
    }
    return ElementRef{
        identifiers,
        std::make_shared<ASTTerm1_Min>(std::make_shared<ASTTerm2_Set>(elements))
    };
}

ElementRef makeMinSet(const SetRef &s) {
    return ElementRef{
        s.identifiers,
        std::make_shared<ASTTerm1_Min>(s.ast)
    };
}


ElementRef makeMaxArgs(nb::args args) {
    Identifiers identifiers;
    SharedASTList elements;
    for (auto arg: args) {
        ElementRef f = nb::cast<ElementRef>(arg);
        identifiers.insert(f.identifiers.begin(), f.identifiers.end());
        elements.push_back(f.ast);
    }
    return ElementRef{
        identifiers,
        std::make_shared<ASTTerm1_Max>(std::make_shared<ASTTerm2_Set>(elements))
    };
}

ElementRef makeMaxSet(const SetRef &s) {
    return ElementRef{
        s.identifiers,
        std::make_shared<ASTTerm1_Max>(s.ast)
    };
}

SetRef makeSetUnion(const SetRef &s1, const SetRef &s2) {
    return SetRef{
        identUnion(s1.identifiers, s2.identifiers),
        std::make_shared<ASTTerm2_Union>(s1.ast, s2.ast)
    };
}

SetRef makeSetDifference(const SetRef &s1, const SetRef &s2) {
    return SetRef{
        identUnion(s1.identifiers, s2.identifiers),
        std::make_shared<ASTTerm2_Setminus>(s1.ast, s2.ast)
    };
}

SetRef makeSetIntersection(const SetRef &s1, const SetRef &s2) {
    return SetRef{
        identUnion(s1.identifiers, s2.identifiers),
        std::make_shared<ASTTerm2_Inter>(s1.ast, s2.ast)
    };
}

bool modelGetBool(const Model &m, const BoolIdent &b) {
    return m.bools.find(lookupSymbol(b))->second;
}

int modelGetInt(const Model &m, const ElementIdent &i) {
    return m.ints.find(lookupSymbol(i))->second;
}

std::set<int> modelGetSet(const Model &m, const SetIdent &s) {
    return m.sets.find(lookupSymbol(s))->second;
}


NB_MODULE(_pymona, m) {
    m.doc() = "Python bindings for the WS1S/WS2S solver MONA";

    nb::class_<Model>(m, "Model")
            .def("__getitem__", &modelGetBool)
            .def("__getitem__", &modelGetInt)
            .def("__getitem__", &modelGetSet)
            .def_ro("bools", &Model::bools)
            .def_ro("ints", &Model::ints)
            .def_ro("sets", &Model::sets);

    nb::class_<BoolRef>(m, "BoolRef")
            .def("dump", [](const BoolRef &f) { f.ast->dump(); });
    nb::class_<BoolIdent, BoolRef>(m, "BoolIdent")
            .def(nb::init<std::string_view>())
            .def("__str__", &lookupSymbol<BoolIdent>);

    nb::class_<ElementRef>(m, "ElementRef")
            .def(nb::init_implicit<int>())
            .def("dump", [](const ElementRef &e) { e.ast->dump(); })
            .def("__add__", &makePlusRightInt,
                 nb::sig("def __add__(self, arg: ElementRef | int) -> ElementRef"))
            .def("__radd__", &makePlusRightInt,
                 nb::sig("def __radd__(self, arg: ElementRef | int) -> ElementRef"))
            .def("__sub__", &makeMinus,
                 nb::sig("def __sub__(self, arg: ElementRef | int) -> ElementRef"))
            .def("__lt__", &makeElementElementFormula<ASTForm_Less>,
                 nb::sig("def __lt__(self, arg: ElementRef | int) -> BoolRef"))
            .def("__le__", &makeElementElementFormula<ASTForm_LessEq>,
                 nb::sig("def __le__(self, arg: ElementRef | int) -> BoolRef"))
            .def("__gt__", &makeGreaterThan,
                 nb::sig("def __gt__(self, arg: ElementRef | int) -> BoolRef"))
            .def("__ge__", &makeGeq,
                 nb::sig("def __ge__(self, arg: ElementRef | int) -> BoolRef"));

    nb::class_<ElementInt, ElementRef>(m, "ElementInt")
            .def(nb::init_implicit<int>())
            .def("__add__", &makePlusLeftInt);
    nb::class_<ElementIdent, ElementRef>(m, "ElementIdent")
            .def(nb::init<std::string_view>())
            .def("__str__", &lookupSymbol<ElementIdent>);

    nb::class_<SetRef>(m, "SetRef")
            .def("dump", [](const SetRef &s) { s.ast->dump(); })
            .def("__le__", &makeSub)
            .def("__ge__", &makeSup)
            .def("__and__", &makeSetIntersection)
            .def("__or__", &makeSetUnion)
            .def("__sub__", &makeSetDifference)
            .def("__call__", &makeNi,
                 nb::sig("def __call__(self, arg: ElementRef | int) -> BoolRef"));
    nb::class_<SetIdent, SetRef>(m, "SetIdent")
            .def(nb::init<std::string_view>())
            .def("__str__", &lookupSymbol<SetIdent>);

    nb::class_<IdentContainer>(m, "IdentContainer")
            .def(nb::init_implicit<BoolIdent>())
            .def(nb::init_implicit<ElementIdent>())
            .def(nb::init_implicit<SetIdent>());

    nb::class_<PredRef>(m, "PredRef")
            .def("__call__", &makePredCall,
                 nb::sig("def __call__(self, *args: BoolRef | ElementRef | int | SetRef) -> BoolRef"))
            .def("__str__", &lookupSymbol<PredRef>)
            .def("__repr__", [](const PredRef &p) {
                return std::format(
                    "<pymona.PredRef `{}` with {} parameters>",
                    lookupSymbol(p),
                    p.n
                );
            });

    m.def("m_int", &makeInt);
    m.def("lt", &makeElementElementFormula<ASTForm_Less>,
          nb::sig("def lt(arg0: ElementRef | int, arg1: ElementRef | int) -> BoolRef"));
    m.def("gt", &makeGreaterThan,
          nb::sig("def gt(arg0: ElementRef | int, arg1: ElementRef | int) -> BoolRef"));
    m.def("leq", &makeElementElementFormula<ASTForm_LessEq>,
          nb::sig("def leq(arg0: ElementRef | int, arg1: ElementRef | int) -> BoolRef"));
    m.def("geq", &makeGeq,
          nb::sig("def geq(arg0: ElementRef | int, arg1: ElementRef | int) -> BoolRef"));

    m.def("empty", &makeEmpty);
    m.def("sub", &makeSub);
    m.def("is_empty", &makeIsEmpty);

    m.def("m_in", &makeIn,
          nb::sig("def m_in(arg0: ElementRef | int, arg1: SetRef) -> BoolRef"));

    m.def("true", &makeTrue);
    m.def("false", &makeFalse);
    m.def("m_and", &makeAnd,
          nb::sig("def m_and(*args: BoolRef) -> BoolRef"));
    m.def("m_or", &makeOr,
          nb::sig("def m_or(*args: BoolRef) -> BoolRef"));
    m.def("implies", &makeImplies);
    m.def("iff", &makeIff);
    m.def("eq", &makeIff)
            .def("eq", &makeElementElementFormula<ASTForm_Equal1>,
                 nb::sig("def eq(arg0: ElementRef | int, arg1: ElementRef | int) -> BoolRef")
            )
            .def("eq", &makeSetEq);
    m.def("neq", &makeNiff)
            .def("neq", &makeElementElementFormula<ASTForm_NotEqual1>,
                 nb::sig("def neq(arg0: ElementRef | int, arg1: ElementRef | int) -> BoolRef")
            )
            .def("neq", &makeSetNeq);
    m.def("m_not", &makeNot);

    m.def("forall1", &makeForall1);
    m.def("forall1", &makeForall1Iter);
    m.def("exists1", &makeExists1);
    m.def("exists1", &makeExists1Iter);

    m.def("forall2", &makeForall2);
    m.def("forall2", &makeForall2Iter);
    m.def("exists2", &makeExists2);
    m.def("exists2", &makeExists2Iter);

    m.def("m_set", &makeSet,
          nb::sig("def m_set(*args: ElementRef | int) -> SetRef"));
    m.def("min", &makeMinSet);
    m.def("min", &makeMinArgs,
          nb::sig("def min(*args: ElementRef | int) -> ElementRef"));
    m.def("max", &makeMaxSet);
    m.def("max", &makeMaxArgs,
          nb::sig("def max(*args: ElementRef | int) -> ElementRef"));

    m.def("solve", &solve);

    m.def("pred", &makePred);
    m.def("macro", &makeMacro);
}
