#include <string_view>
#include <utility>
#include <variant>
#include <format>

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

Identifiers set_union(const Identifiers &i1, const Identifiers &i2) {
    Identifiers result(i1);
    result.insert(i2.begin(), i2.end());
    return std::move(result);
}

struct IdentContainer {
    Ident ident;
};

struct BoolRef {
    Identifiers identifiers;
    ASTFormPtr form;
};

struct BoolIdent : BoolRef, IdentContainer {
    BoolIdent(std::string_view name)
        : BoolIdent(addVar(name, Varname0)) {
    }

    BoolIdent(Ident identt)
        : BoolRef{
              Identifiers{identt},
              std::make_shared<ASTForm_Var0>(identt)
          }, IdentContainer{identt} {
    }
};

struct ElementRef {
    ElementRef(int i)
        : term(std::make_shared<ASTTerm1_Int>(i)) {
    }

    ElementRef(Identifiers identifiers, ASTTerm1Ptr term)
        : identifiers(std::move(identifiers)),
          term(std::move(term)) {
    }

    Identifiers identifiers;
    ASTTerm1Ptr term;
};

struct ElementIdent : ElementRef, IdentContainer {
    ElementIdent(std::string_view name)
        : ElementIdent(addVar(name, Varname1)) {
    }

    ElementIdent(Ident identt)
        : ElementRef(
              Identifiers{identt},
              std::make_shared<ASTTerm1_Var1>(identt)
          ), IdentContainer{identt} {
    }
};

struct SetRef {
    Identifiers identifiers;
    ASTTerm2Ptr term;
};

struct SetIdent : SetRef, IdentContainer {
    SetIdent(std::string_view name)
        : SetIdent(addVar(name, Varname2)) {
    }

    SetIdent(Ident identt)
        : SetRef{
              Identifiers{identt},
              std::make_shared<ASTTerm2_Var2>(identt)
          }, IdentContainer{identt} {
    }
};

ElementRef makeInt(int i) {
    return i;
}

BoolRef makeLessThan(const ElementRef &i1, const ElementRef &i2) {
    return BoolRef{
        set_union(i1.identifiers, i2.identifiers),
        std::make_shared<ASTForm_Less>(i1.term, i2.term, dummyPos)
    };
}

BoolRef makeLeq(const ElementRef &i1, const ElementRef &i2) {
    return BoolRef{
        set_union(i1.identifiers, i2.identifiers),
        std::make_shared<ASTForm_LessEq>(i1.term, i2.term)
    };
}

BoolRef makeSub(const SetRef &s1, const SetRef &s2) {
    return BoolRef{
        set_union(s1.identifiers, s2.identifiers),
        std::make_shared<ASTForm_Sub>(s1.term, s2.term)
    };
}

BoolRef makeIn(const ElementRef &e, const SetRef &s) {
    return BoolRef{
        set_union(e.identifiers, s.identifiers),
        std::make_shared<ASTForm_In>(e.term, s.term, dummyPos)
    };
}

BoolRef makeTrue() {
    return BoolRef{
        std::set<Ident>(),
        std::make_shared<ASTForm_True>(dummyPos)
    };
}

BoolRef makeFalse() {
    return BoolRef{
        std::set<Ident>(),
        std::make_shared<ASTForm_False>(dummyPos)
    };
}

BoolRef makeAnd(nb::args args) {
    Identifiers identifiers;
    ASTFormPtr result = std::make_shared<ASTForm_True>(dummyPos);
    for (auto arg: args) {
        BoolRef f = nb::cast<BoolRef>(arg);
        identifiers.insert(f.identifiers.begin(), f.identifiers.end());
        result = std::make_shared<ASTForm_And>(
            std::move(result), f.form, dummyPos
        );
    }
    return BoolRef{identifiers, std::move(result)};
}

BoolRef makeOr(nb::args args) {
    Identifiers identifiers;
    ASTFormPtr result = std::make_shared<ASTForm_False>(dummyPos);
    for (auto arg: args) {
        BoolRef f = nb::cast<BoolRef>(arg);
        identifiers.insert(f.identifiers.begin(), f.identifiers.end());
        result = std::make_shared<ASTForm_Or>(
            std::move(result), f.form, dummyPos
        );
    }
    return BoolRef{identifiers, std::move(result)};
}

BoolRef makeImplies(const BoolRef &f1, const BoolRef &f2) {
    return BoolRef{
        set_union(f1.identifiers, f2.identifiers),
        std::make_shared<ASTForm_Impl>(f1.form, f2.form, dummyPos)
    };
}

BoolRef makeIff(const BoolRef &f1, const BoolRef &f2) {
    return BoolRef{
        set_union(f1.identifiers, f2.identifiers),
        std::make_shared<ASTForm_Biimpl>(f1.form, f2.form)
    };
}

BoolRef makeNot(const BoolRef &f) {
    return BoolRef{
        f.identifiers,
        std::make_shared<ASTForm_Not>(f.form, dummyPos)
    };
}

BoolRef makeForall1(const ElementIdent &id, const BoolRef &f) {
    IdentList *list = new IdentList(id.ident);
    return BoolRef{
        set_union(id.identifiers, f.identifiers),
        std::make_shared<ASTForm_All1>(nullptr, list, f.form)
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
        std::make_shared<ASTForm_All1>(nullptr, list, f.form)
    };
}

BoolRef makeExists1(const ElementIdent &id, const BoolRef &f) {
    IdentList *list = new IdentList(id.ident);
    return BoolRef{
        set_union(id.identifiers, f.identifiers),
        std::make_shared<ASTForm_Ex1>(nullptr, list, f.form)
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
        std::make_shared<ASTForm_Ex1>(nullptr, list, f.form)
    };
}

BoolRef makeForall2(const SetIdent &id, const BoolRef &f) {
    IdentList *list = new IdentList(id.ident);
    return BoolRef{
        set_union(id.identifiers, f.identifiers),
        std::make_shared<ASTForm_All2>(nullptr, list, f.form)
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
        std::make_shared<ASTForm_All2>(nullptr, list, f.form)
    };
}

BoolRef makeExists2(const SetIdent &id, const BoolRef &f) {
    IdentList *list = new IdentList(id.ident);
    return BoolRef{
        set_union(id.identifiers, f.identifiers),
        std::make_shared<ASTForm_Ex2>(nullptr, list, f.form)
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
        std::make_shared<ASTForm_Ex2>(nullptr, list, f.form)
    };
}

std::optional<Model> solve(const BoolRef &formula) {
    MonaAST ast{formula.form};
    for (const auto ident: formula.identifiers) {
        ast.globals.insert(ident);
    }
    return getModel(ast);
}

template<typename T>
std::string_view lookupSymbol(const T &container) {
    return symbolTable.lookupSymbol(container.ident);
}

struct PredRef : IdentContainer {
    int n;
};

PredRef makePred(
    std::string_view name,
    nb::typed<nb::iterable, std::variant<BoolIdent, ElementIdent, SetIdent> > ids,
    const BoolRef &f
) {
    IdentList *list = new IdentList;
    for (auto id: nb::iter(ids)) {
        Ident ident = nb::cast<IdentContainer>(id).ident;
        list->insert(ident);
    }

    int n = list->size();

    Ident pred = addPredicate(name);

    IdentList *bound = list->copy(), *frees = new IdentList;
    f.form->freeVars(frees, bound);

    predicateLib.insert(
        bound,
        frees,
        list,
        f.form,
        false,
        pred
    );

    return PredRef{pred, n};
}

BoolRef makePredCall(const PredRef &pred, nb::args args) {
    Identifiers identifiers;
    SharedASTList salist;
    for (auto arg: args) {
        if (nb::isinstance<BoolRef>(arg)) {
            const auto &ref = nb::cast<const BoolRef &>(arg);
            identifiers.insert(ref.identifiers.begin(), ref.identifiers.end());
            salist.push_back(ref.form);
        } else if (nb::isinstance<ElementRef>(arg)) {
            const auto &ref = nb::cast<const ElementRef &>(arg);
            identifiers.insert(ref.identifiers.begin(), ref.identifiers.end());
            salist.push_back(ref.term);
        } else if (nb::isinstance<SetRef>(arg)) {
            const auto &ref = nb::cast<const SetRef &>(arg);
            identifiers.insert(ref.identifiers.begin(), ref.identifiers.end());
            salist.push_back(ref.term);
        } else {
            throw nanobind::value_error("Bad argument passed to predicate");
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
                "Wrong number of parameters to {}",
                symbolTable.lookupSymbol(id)
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


NB_MODULE(_pymona, m) {
    m.doc() = "Python bindings for the WS1S/WS2S solver MONA";

    nb::class_<BoolRef>(m, "BoolRef");
    nb::class_<BoolIdent, BoolRef>(m, "BoolIdent")
            .def(nb::init<std::string_view>())
            .def("__str__", &lookupSymbol<BoolIdent>);

    nb::class_<ElementRef>(m, "ElementRef")
            .def(nb::init_implicit<int>());
    nb::class_<ElementIdent, ElementRef>(m, "ElementIdent")
            .def(nb::init<std::string_view>())
            .def("__str__", &lookupSymbol<ElementIdent>);

    nb::class_<SetRef>(m, "SetRef");
    nb::class_<SetIdent, SetRef>(m, "SetIdent")
            .def(nb::init<std::string_view>())
            .def("__str__", &lookupSymbol<SetIdent>);

    nb::class_<IdentContainer>(m, "IdentContainer")
            .def(nb::init_implicit<BoolIdent>())
            .def(nb::init_implicit<ElementIdent>())
            .def(nb::init_implicit<SetIdent>());

    nb::class_<PredRef>(m, "PredRef")
            .def("__call__", &makePredCall)
            .def("__str__", &lookupSymbol<PredRef>);

    m.def("m_int", &makeInt);
    m.def("less_than", &makeLessThan,
          nb::sig("def less_than(arg0: ElementRef | int, arg1: ElementRef | int) -> BoolRef"));
    m.def("leq", &makeLeq,
          nb::sig("def leq(arg0: ElementRef | int, arg1: ElementRef | int) -> BoolRef"));
    m.def("sub", &makeSub);

    m.def("m_in", &makeIn);

    m.def("true", &makeTrue);
    m.def("false", &makeFalse);
    m.def("m_and", &makeAnd);
    m.def("m_or", &makeOr);
    m.def("implies", &makeImplies);
    m.def("iff", &makeIff);
    m.def("m_not", &makeNot);

    m.def("forall1", &makeForall1);
    m.def("forall1", &makeForall1Iter);
    m.def("exists1", &makeExists1);
    m.def("exists1", &makeExists1Iter);

    m.def("forall2", &makeForall2);
    m.def("forall2", &makeForall2Iter);
    m.def("exists2", &makeExists2);
    m.def("exists2", &makeExists2Iter);

    m.def("solve", &solve);

    m.def("pred", &makePred);
}
