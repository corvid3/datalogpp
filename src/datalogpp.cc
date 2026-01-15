#include <algorithm>
#include <map>
#include <optional>
#include <sstream>
#include <stdexcept>
#include <utility>
#include <variant>

#include "datalogpp.hh"

/*

  SomePredicate(X, Y, Z).

*/

namespace datalogpp {

Predicate::Predicate(std::string_view name, int arity)
  : m_name(name)
  , m_arity(arity) {};

std::string_view
Predicate::name() const
{
  return m_name;
}

int
Predicate::arity() const
{
  return m_arity;
}

void
Predicate::add(std::span<const Value> vals)
{
  if ((int)vals.size() != m_arity)
    throw std::runtime_error(
      "provided list of values to add_fact does not match arity");

  m_baseFacts.insert(Fact(vals.begin(), vals.end()));
}

void
Predicate::add(std::span<const Term> terms,
               std::span<const Atom> atoms,
               inequality_map const& map)
{
  if ((int)terms.size() != m_arity)
    throw std::runtime_error(
      "when adding rule to predicate, terms.size() != arity");

  m_rules.push_back(Rule(Atom(m_name, terms), atoms, map));
}

bool
Predicate::query_fact(std::span<Value const> vals)
{
  for (auto const& fact : m_baseFacts)
    if (std::ranges::equal(vals, fact))
      return true;

  for (auto const& fact : m_derivedFacts)
    if (std::ranges::equal(vals, fact))
      return true;

  return false;
}

Predicate&
Interpreter::predicate(std::string_view name, int arity)
{
  if (m_predicates.contains(name))
    throw std::runtime_error("attempting to overwrite predicate name");

  return m_predicates.emplace(std::string(name), Predicate(name, arity))
    .first->second;
}

std::optional<std::reference_wrapper<Predicate>>
Interpreter::get_predicate(std::string_view what)
{
  if (not m_predicates.contains(what))
    return std::nullopt;

  return m_predicates.find(what)->second;
}

void
Interpreter::infer()
{
  // when starting a new infer step,
  // everything needs to be treated as new information
  for (auto& [_, pred] : m_predicates) {
    pred.m_newlyDerivedFacts.insert(pred.m_derivedFacts.begin(),
                                    pred.m_derivedFacts.end());
    pred.m_derivedFacts.clear();
  }

  for (;;) {
    std::list<std::pair<Predicate*, Fact>> new_facts;

    for (auto& [_, pred] : m_predicates) {
      for (auto& rule : pred.m_rules) {
        // std::cout << std::format(
        //   "{}::{}\n", pred.name(), rule.head.predicate());
        for (auto& subst :
             this->evaluate(rule.body, rule.inequality_assertions)) {
          Fact f;

          for (auto const& term : rule.head.subterms()) {
            if (std::holds_alternative<Var>(term)) {
              if (!subst.contains(std::get<Var>(term)))
                throw std::runtime_error(std::format(
                  "datalogpp: head substitution variable {} failed to unify",
                  std::get<Var>(term).m_name));
              f.push_back(subst.at(std::get<Var>(term)));
            } else
              f.push_back(std::get<Value>(term));
          }

          if (not pred.m_derivedFacts.contains(f) and
              not pred.m_newlyDerivedFacts.contains(f) and
              not pred.m_baseFacts.contains(f))
            new_facts.push_back({ &pred, f });
        }
      }
    }

    // std::cout << std::format("gen {}: num: {}\n", gen, new_facts.size());

    for (auto& [_, pred] : m_predicates) {
      // std::cout << std::format(
      //   "pred: {}, new: {}\n", pred.m_name, pred.m_newlyDerivedFacts.size());

      pred.m_derivedFacts.insert(pred.m_newlyDerivedFacts.begin(),
                                 pred.m_newlyDerivedFacts.end());
      pred.m_newlyDerivedFacts.clear();
    }

    if (new_facts.empty())
      break;

    for (auto& [p, f] : new_facts) {
      p->m_newlyDerivedFacts.insert(f);
    }
  }
}

auto
Interpreter::query(std::span<Atom const> atoms,
                   inequality_map const& inequality_assertions)
  -> std::vector<Substitution>
{
  Substitution in;
  // not _actually_ naive evaluation,
  // just a hack to get querying working properly
  return search(true, 0, atoms, inequality_assertions, in);
}

auto
Interpreter::evaluate(std::span<Atom const> atoms,
                      inequality_map const& inequality_assertions)
  -> std::vector<Substitution>
{
  Substitution in;
  return search(false, 0, atoms, inequality_assertions, in);
}

auto
Interpreter::search(bool naive,
                    int i,
                    std::span<Atom const> atoms,
                    inequality_map const& inequality_assertions,
                    Substitution& subst) -> std::vector<Substitution>
{
  if (i == (int)atoms.size())
    return { subst };

  std::vector<Substitution> out;

  auto const atom = atoms[i];
  auto const predicate_name = atom.predicate();
  auto const predicate = m_predicates.find(predicate_name);

  if (predicate == m_predicates.end())
    throw std::runtime_error(
      std::format("unknown predicate {}", predicate_name));

  auto const& base_facts = predicate->second.m_baseFacts;
  auto const& derived_facts = naive ? predicate->second.m_derivedFacts
                                    : predicate->second.m_newlyDerivedFacts;

  for (auto const& fact : base_facts) {
    Substitution copy = subst;

    if (unify(atom, fact, inequality_assertions, copy)) {
      auto const m = search(naive, i + 1, atoms, inequality_assertions, copy);
      out.insert(out.begin(), m.begin(), m.end());
    }
  }

  for (auto const& fact : derived_facts) {
    Substitution copy = subst;

    if (unify(atom, fact, inequality_assertions, copy)) {
      auto const m = search(naive, i + 1, atoms, inequality_assertions, copy);
      out.insert(out.begin(), m.begin(), m.end());
    }
  }

  return out;
}

bool
Interpreter::unify(Atom atom,
                   Fact fact,
                   inequality_map const& inequality_assertions,
                   Substitution& subst)
{
  auto const& st = atom.subterms();

  if (st.size() != fact.size())
    throw std::runtime_error("attempting to unity atom with mismatched fact");

  for (auto i = 0; i < (int)st.size(); i++) {
    auto const t = st[i];
    auto const v = fact[i];

    if (std::holds_alternative<Var>(t)) {
      auto const& tv = std::get<Var>(t);

      if (subst.contains(tv) and (std::string_view(tv) != "_") and
          subst.at(tv) != v)
        return false;

      if (inequality_assertions.contains(tv)) {
        auto const& what = inequality_assertions.at(tv);
        if (std::holds_alternative<Value>(what))
          if (v == std::get<Value>(what))
            return false;

        if (std::holds_alternative<Var>(what)) {
          auto const& rhs_var = std::get<Var>(what);
          if (subst.contains(rhs_var) and subst[rhs_var] == v)
            return false;
        }
      }

      subst[tv] = v;
    } else if (std::get<Value>(t) != v)
      return false;
  }

  return true;
}

std::string
Interpreter::dump_facts()
{
  std::stringstream ss;

  ss << "[[BASE FACTS]]\n";

  for (auto const& [_, p] : m_predicates) {
    for (auto const& b : p.m_baseFacts) {
      ss << p.name() << '(';

      for (unsigned i = 0; i < b.size(); i++) {
        ss << b[i];

        if (i != b.size() - 1)
          ss << ", ";
      }

      ss << ").\n";
    }
  }

  ss << "\n[[DERIVED FACTS]]\n";

  for (auto const& [_, p] : m_predicates) {
    for (auto const& b : p.m_derivedFacts) {
      ss << p.name() << '(';

      for (unsigned i = 0; i < b.size(); i++) {
        ss << b[i];

        if (i != b.size() - 1)
          ss << ", ";
      }

      ss << ").\n";
    }
  }

  return std::move(ss).str();
}

}; // namespace datalogpp
