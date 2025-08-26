#pragma once

#include <algorithm>
#include <concepts>
#include <functional>
#include <initializer_list>
#include <list>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <span>
#include <stdexcept>
#include <string>
#include <string_view>
#include <tuple>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

namespace datalogpp {

// TODO: embetter the ergonomics,
// perhaps wrap all rule/fact modification within some
// lambdas w/ accessor structs as parameters,
// and then force infer of the engine at the end
// of execution?

class Interpreter;

class Var
{
public:
  explicit constexpr Var(std::string_view name)
    : m_name(name) {};

  constexpr operator std::string_view() const { return m_name; }

  constexpr bool operator<(Var const& rhs) const
  {
    return std::hash<std::string_view>()(m_name) <
           std::hash<std::string_view>()(rhs.m_name);
  }

private:
  friend class Interpreter;

  std::string m_name;
};

Var inline
operator""_V(char const* in, std::size_t const)
{
  return Var(in);
}

using Value = std::string;
using Term = std::variant<Var, Value>;
using Fact = std::vector<Value>;
using inequality_map = std::map<Var, Term>;

class Atom
{
public:
  Atom(std::string_view name, std::span<Term const> parameters)
    : m_predicateName(name)
    , m_subterms(parameters.begin(), parameters.end())
  {
  }

  Atom(std::string_view name, std::initializer_list<Term const> params)
    : Atom(name, std::span(params))
  {
  }

  bool ground() const
  {
    for (auto const& term : m_subterms)
      if (std::holds_alternative<Var>(term))
        return false;

    return true;
  }

  std::span<Term const> subterms() const { return m_subterms; }
  std::string_view predicate() const { return m_predicateName; }

private:
  std::string m_predicateName;
  std::vector<Term> m_subterms;
};

auto inline
operator""_p(char const* in, unsigned long)
{
  return [=](auto&&... ps) { return Atom(in, { ps... }); };
}

struct Inequality
{
  Inequality(Var head, Term term)
    : head(std::move(head))
    , term(std::move(term)) {};

  Var head;
  Term term;
};

template<typename T>
concept is_ineq_assert = requires(T t) {
  { Inequality{ t } } -> std::same_as<T>;
};

struct Rule
{
  Atom head;
  std::vector<Atom> body;
  inequality_map inequality_assertions;

  Rule(Atom head, std::span<Atom const> body, inequality_map map)
    : head(head)
    , body(body.begin(), body.end())
  {
    inequality_assertions = map;
  };

  // fact
  Rule(Atom head)
    : head(head)
  {
  }

  bool is_ground() const
  {
    bool ground = head.ground();

    for (auto const& atom : body)
      ground &= atom.ground();

    return ground;
  }
};

template<typename L, typename R>
struct Goofyness;

template<typename... Atoms, typename... Assertions>
struct Goofyness<std::tuple<Atoms...>, std::tuple<Assertions...>>
{
  Goofyness(std::tuple<Atoms...> const&& atoms,
            std::tuple<Assertions...> const&& asserts)
    : atoms(atoms)
    , assertions(asserts) {};

  std::tuple<Atoms...> atoms;
  std::tuple<Assertions...> assertions;
};

inline auto
operator+(Atom const& lhs, Atom const& rhs)
{
  return Goofyness<std::tuple<Atom, Atom>, std::tuple<>>({ lhs, rhs }, {});
}

inline auto
operator+(Atom const& lhs, Inequality const& rhs)
{
  return Goofyness<std::tuple<Atom>, std::tuple<Inequality>>(std::tuple{ lhs },
                                                             std::tuple{ rhs });
}

template<typename L, typename R>
inline auto
operator+(Goofyness<L, R> const& lhs, Atom const& rhs)
{
  return Goofyness<decltype(std::tuple_cat(std::move(lhs.atoms),
                                           std::make_tuple(rhs))),
                   decltype(lhs.assertions)>(
    std::tuple_cat(std::move(lhs.atoms), std::make_tuple(rhs)),
    std::move(lhs.assertions));
  // return Goofyness<decltype(std::tuple_cat(std::declval<L>(),
  //                                          std::declval<Atom>())),
  //                                          R>(std::tupleeca)
}

template<typename L, typename R>
inline auto
operator+(Goofyness<L, R> const& lhs, Inequality const& rhs)
{
  // return Goofyness<decltype(lhs.atoms),
  //                  decltype(std::tuple_cat(
  //                    lhs.assertions, std::tuple{ InequalityAssertion(rhs)
  //                    }))>(
  return Goofyness<decltype(lhs.atoms),
                   decltype(std::tuple_cat(std::move(lhs.assertions),
                                           std::make_tuple(rhs)))>(
    std::move(lhs.atoms), std::tuple_cat(lhs.assertions, std::make_tuple(rhs)));
}

// inline auto operator,(Atom const& lhs, Atom const& rhs)
// {
//   return std::make_tuple(lhs, rhs);
// }

// template<typename... Ts>
// inline auto operator,(std::tuple<Ts...> const& lhs, Atom const& rhs)
// {
//   return std::tuple_cat(lhs, std::make_tuple(rhs));
// }

class Predicate
{
  template<typename... Ts>
  auto static constexpr tuple_to_array_term(std::tuple<Ts...> what)
  {
    return std::apply([](auto&&... in) { return std::array{ Term(in)... }; },
                      what);
  }

  template<typename... Ts>
  auto static constexpr tuple_to_array(std::tuple<Ts...> what)
  {
    return std::apply([](auto&&... in) { return std::array{ in... }; }, what);
  }

  template<typename... Ts>
  auto static constexpr ineq_to_map(std::tuple<Ts...> what)
  {
    return std::apply(
      [](auto&&... in) { return inequality_map({ { in.head, in.term }... }); },
      what);
  }

  template<typename... Ts>
  struct RuleAdder
  {
    struct fact_hack
    {};

    RuleAdder(Predicate& p, std::tuple<Ts...> const& terms)
      : m_pred(p)
      , m_terms(tuple_to_array_term(terms))
    {
    }

    RuleAdder(Predicate& p)
      : m_pred(p)
    {
    }

    void operator=(fact_hack)
    {
      std::array<Value, sizeof...(Ts)> vals;
      std::ranges::transform(
        m_terms, vals.begin(), [](auto&& in) { return std::get<Value>(in); });

      m_pred.add(vals);
    }

    void operator=(Atom const& atom) &&
    {
      m_pred.add(m_terms, std::array{ atom }, {});
    }

    template<typename L, typename R>
    void operator=(Goofyness<L, R> const& goofy) &&
    {

      m_pred.add(
        m_terms, tuple_to_array(goofy.atoms), ineq_to_map(goofy.assertions));
    }

    Predicate& m_pred;
    std::array<Term, sizeof...(Ts)> m_terms;
  };

public:
  std::string_view name() const;
  int arity() const;

  void add(std::span<Value const> vals);
  void add(std::span<Term const> terms,
           std::span<Atom const> atoms,
           inequality_map const& map);

  void add(std::initializer_list<Value const> vals) { add(std::span(vals)); }

  void add(std::initializer_list<Term const> terms,
           std::initializer_list<Atom const> atoms)
  {
    add(std::span(terms), std::span(atoms), {});
  }

  bool query_fact(std::span<Value const> vals);
  bool query_fact(std::initializer_list<Value const> vals)
  {
    return query_fact(std::span(vals));
  }

  auto operator()()
  {
    if (m_arity != 0)
      throw std::runtime_error("arity of predicate is mismatched");

    return RuleAdder(*this);
  };
  auto operator()(auto... terms)
  {
    if (sizeof...(terms) != m_arity)
      throw std::runtime_error("arity of predicate is mismatched");

    return RuleAdder(*this, std::tuple(terms...));
  }

private:
  Predicate(std::string_view name, int arity);

  std::string const m_name;
  int const m_arity;

  // staging for newly derived facts
  // see the `infer` method
  std::set<Fact> m_baseFacts;
  std::set<Fact> m_derivedFacts;
  std::set<Fact> m_newlyDerivedFacts;

  std::list<Rule> m_rules;

  friend class Interpreter;
};

class Interpreter
{
  using Substitution = std::map<Var, Value>;

public:
  Interpreter() = default;

  // parses syntax to create rules and definitions
  void execute(std::string_view);

  Predicate& predicate(std::string_view name, int arity);
  std::optional<std::reference_wrapper<Predicate>> get_predicate(
    std::string_view what);

  void infer();
  std::vector<Substitution> query(
    std::span<Atom const>,
    inequality_map const& inequality_assertions = {});

  // creates a formatted string
  // that dumps every fact in the database
  std::string dump_facts();

private:
  std::vector<Substitution> evaluate(
    std::span<Atom const> atoms,
    inequality_map const& inequality_assertions);
  std::vector<Substitution> search(bool naive,
                                   int i,
                                   std::span<Atom const> atoms,
                                   inequality_map const& inequality_assertions,
                                   Substitution& subst);

  bool unify(Atom atom,
             Fact fact,
             inequality_map const& inequality_assertions,
             Substitution& subst);
  std::map<std::string, Predicate, std::less<>> m_predicates;
};

};
