#ifndef __UTIL_IMMUTABLEMAP_H__
#define __UTIL_IMMUTABLEMAP_H__
#include <functional>
#include <cassert>
#include <vector>
namespace klee {
  template<class K, class V, class KOV, class CMP>
  class ImmutableTree {
  public:
    static size_t allocated;
    class iterator;
    typedef K key_type;
    typedef V value_type;
    typedef KOV key_of_value;
    typedef CMP key_compare;
  public:
    ImmutableTree() : node(Node::terminator.incref()) { }
    ImmutableTree(const ImmutableTree &s) : node(s.node->incref()) { }
    ~ImmutableTree() { node->decref(); }
    ImmutableTree &operator=(const ImmutableTree &s) {
      Node *n = s.node->incref();
      node->decref();
      node = n;
      return *this;
    }
    const value_type *lookup(const key_type &k) const {
      Node *n = node;
      while (!n->isTerminator()) {
        key_type key = key_of_value()(n->value);
        if (key_compare()(k, key)) {
          n = n->left;
        } else if (key_compare()(key, k)) {
          n = n->right;
        } else {
          return &n->value;
        }
      }
      return 0;
    }
    const value_type *lookup_previous(const key_type &k) const {
      Node *n = node;
      Node *result = 0;
      while (!n->isTerminator()) {
        key_type key = key_of_value()(n->value);
        if (key_compare()(k, key)) {
          n = n->left;
        } else if (key_compare()(key, k)) {
          result = n;
          n = n->right;
        } else {
          return &n->value;
        }
      }
      return result ? &result->value : 0;
    }
    size_t size() const { return node->size(); }
    ImmutableTree insert(const value_type &value) const { return ImmutableTree(node->insert(value)); }
    ImmutableTree replace(const value_type &value) const { return ImmutableTree(node->replace(value)); }
    ImmutableTree remove(const key_type &key) const { return ImmutableTree(node->remove(key)); }
    ImmutableTree popMin(value_type &valueOut) const { return ImmutableTree(node->popMin(valueOut)); }
    iterator begin() const { return iterator(node, true); }
    iterator end() const { return iterator(node, false); }
    iterator lower_bound(const key_type &k) const {
      iterator it(node,false);
      for (Node *root=node; !root->isTerminator();) {
        it.stack.push_back(root);
        if (key_compare()(k, key_of_value()(root->value))) {
          root = root->left;
        } else if (key_compare()(key_of_value()(root->value), k)) {
          root = root->right;
        } else {
          return it;
        }
      }
      if (!it.stack.empty()) {
        Node *last = it.stack.back();
        if (key_compare()(key_of_value()(last->value), k))
          ++it;
      }
      return it;
    }
    iterator upper_bound(const key_type &key) const {
      iterator end(node,false),it = lower_bound(key);
      if (it!=end && !key_compare()(key,key_of_value()(*it)))
        ++it;
      return it;
    }
    static size_t getAllocated() { return allocated; }
  private:
    class Node;
    Node *node;
    ImmutableTree(Node *_node) : node(_node) { }
  };
  template<class K, class V, class KOV, class CMP>
  class ImmutableTree<K,V,KOV,CMP>::Node {
  public:
    static Node terminator;
    Node *left, *right;
    value_type value;
    unsigned height, references;
  protected:
    Node() : left(&terminator), right(&terminator), height(0), references(3) { assert(this==&terminator); }
    static Node *balance(Node *left, const value_type &value, Node *right) {
      if (left->height > right->height + 2) {
        Node *ll = left->left;
        Node *lr = left->right;
        if (ll->height >= lr->height) {
          Node *nlr = new Node(lr->incref(), right, value);
          Node *res = new Node(ll->incref(), nlr, left->value);
          left->decref();
          return res;
        } else {
          Node *lrl = lr->left;
          Node *lrr = lr->right;
          Node *nll = new Node(ll->incref(), lrl->incref(), left->value);
          Node *nlr = new Node(lrr->incref(), right, value);
          Node *res = new Node(nll, nlr, lr->value);
          left->decref();
          return res;
        }
      } else if (right->height > left->height + 2) {
        Node *rl = right->left;
        Node *rr = right->right;
        if (rr->height >= rl->height) {
          Node *nrl = new Node(left, rl->incref(), value);
          Node *res = new Node(nrl, rr->incref(), right->value);
          right->decref();
          return res;
        } else {
          Node *rll = rl->left;
          Node *rlr = rl->right;
          Node *nrl = new Node(left, rll->incref(), value);
          Node *nrr = new Node(rlr->incref(), rr->incref(), right->value);
          Node *res = new Node(nrl, nrr, rl->value);
          right->decref();
          return res;
        }
      } else {
        return new Node(left, right, value);
      }
    }
  public:
    Node(Node *_left, Node *_right, const value_type &_value)
      : left(_left), right(_right), value(_value), 
        height(std::max(left->height, right->height) + 1), references(1) {
      ++allocated;
    }
    ~Node() {
      left->decref();
      right->decref();
      --allocated;
    }
    void decref() {
      --references;
      if (references==0) delete this;
    }
    Node *incref() {
      ++references;
      return this;
    }
    bool isTerminator() { return this==&terminator; }
    size_t size() {
      if (isTerminator()) {
        return 0;
      } else {
        return left->size() + 1 + right->size();
      }
    }
    Node *popMin(value_type &valueOut) {
      if (left->isTerminator()) {
        valueOut = value;
        return right->incref();
      } else {
        return balance(left->popMin(valueOut), value, right->incref());
      }
    }
    Node *insert(const value_type &v) {
      if (isTerminator()) {
        return new Node(terminator.incref(), terminator.incref(), v);
      } else {
        if (key_compare()(key_of_value()(v), key_of_value()(value))) {
          return balance(left->insert(v), value, right->incref());
        } else if (key_compare()(key_of_value()(value), key_of_value()(v))) {
          return balance(left->incref(), value, right->insert(v));
        } else {
          return incref();
        }
      }
    }
    Node *replace(const value_type &v) {
      if (isTerminator()) {
        return new Node(terminator.incref(), terminator.incref(), v);
      } else {
        if (key_compare()(key_of_value()(v), key_of_value()(value))) {
          return balance(left->replace(v), value, right->incref());
        } else if (key_compare()(key_of_value()(value), key_of_value()(v))) {
          return balance(left->incref(), value, right->replace(v));
        } else {
          return new Node(left->incref(), right->incref(), v);
        }
      }
    }
    Node *remove(const key_type &k) {
      if (isTerminator()) {
        return incref();
      } else {
        if (key_compare()(k, key_of_value()(value))) {
          return balance(left->remove(k), value, right->incref());
        } else if (key_compare()(key_of_value()(value), k)) {
          return balance(left->incref(), value, right->remove(k));
        } else {
          if (left->isTerminator()) {
            return right->incref();
          } else if (right->isTerminator()) {
            return left->incref();
          } else {
            value_type min;
            Node *nr = right->popMin(min);
            return balance(left->incref(), min, nr);
          }
        }
      }
    }
  };
  template<typename T>
  class FixedStack {
    unsigned pos, max;
    T *elts;
  public:
    FixedStack(unsigned _max) : pos(0), max(_max), elts(new T[max]) {}
    FixedStack(const FixedStack &b) : pos(b.pos), max(b.max), elts(new T[b.max]) {
      std::copy(b.elts, b.elts+pos, elts);
    }
    ~FixedStack() { delete[] elts; }
    void push_back(const T &elt) { elts[pos++] = elt; }
    void pop_back() { --pos; }
    bool empty() { return pos==0; }
    T &back() { return elts[pos-1]; }
    FixedStack &operator=(const FixedStack &b) {
      assert(max == b.max); 
      pos = b.pos;
      std::copy(b.elts, b.elts+pos, elts);
      return *this;
    }
    bool operator==(const FixedStack &b) {
      return (pos == b.pos && std::equal(elts, elts+pos, b.elts));
    }
    bool operator!=(const FixedStack &b) { return !(*this==b); }
  };
  template<class K, class V, class KOV, class CMP>
  class ImmutableTree<K,V,KOV,CMP>::iterator {
    friend class ImmutableTree<K,V,KOV,CMP>;
  private:
    Node *root; 
    FixedStack<Node*> stack;
  public:
    iterator(Node *_root, bool atBeginning) : root(_root->incref()), stack(root->height) {
      if (atBeginning) {
        for (Node *n=root; !n->isTerminator(); n=n->left)
          stack.push_back(n);
      }
    }
    iterator(const iterator &i) : root(i.root->incref()), stack(i.stack) { }
    ~iterator() { root->decref(); }
    iterator &operator=(const iterator &b) {
      b.root->incref();
      root->decref();
      root = b.root;
      stack = b.stack;
      return *this;
    }
    const value_type &operator*() {
      Node *n = stack.back();
      return n->value;
    }
    const value_type *operator->() {
      Node *n = stack.back();
      return &n->value;
    }
    bool operator==(const iterator &b) { return stack==b.stack; }
    bool operator!=(const iterator &b) { return stack!=b.stack; }
    iterator &operator--() {
      if (stack.empty()) {
        for (Node *n=root; !n->isTerminator(); n=n->right)
          stack.push_back(n);
      } else {
        Node *n = stack.back();
        if (n->left->isTerminator()) {
          for (;;) {
            Node *prev = n;
            stack.pop_back();
            if (stack.empty()) {
              break;
            } else {
              n = stack.back();
              if (prev==n->right)
                break;
            }
          }
        } else {
          stack.push_back(n->left);
          for (n=n->left->right; !n->isTerminator(); n=n->right)
            stack.push_back(n);
        }
      }
      return *this;
    }
    iterator &operator++() {
      assert(!stack.empty());
      Node *n = stack.back();
      if (n->right->isTerminator()) {
        for (;;) {
          Node *prev = n;
          stack.pop_back();
          if (stack.empty()) {
            break;
          } else {
            n = stack.back();
            if (prev==n->left)
              break;
          }
        }
      } else {
        stack.push_back(n->right);
        for (n=n->right->left; !n->isTerminator(); n=n->left)
          stack.push_back(n);
      }
      return *this;
    }
  };
  /***/
  template<class K, class V, class KOV, class CMP> 
  typename ImmutableTree<K,V,KOV,CMP>::Node 
  ImmutableTree<K,V,KOV,CMP>::Node::terminator;
  template<class K, class V, class KOV, class CMP> 
  size_t ImmutableTree<K,V,KOV,CMP>::allocated = 0;
  template<class V, class D>
  struct _Select1st {
    D &operator()(V &a) const { return a.first; }
    const D &operator()(const V &a) const { return a.first; }
  };
  template<class K, class D, class CMP=std::less<K> >
  class ImmutableMap {
  public:
    typedef K key_type;
    typedef std::pair<K,D> value_type;
    typedef ImmutableTree<K, value_type, _Select1st<value_type,key_type>, CMP> Tree;
    typedef typename Tree::iterator iterator;
  private:
    Tree elts;
    ImmutableMap(const Tree &b): elts(b) {}
  public:
    ImmutableMap() {}
    ImmutableMap(const ImmutableMap &b) : elts(b.elts) {}
    ~ImmutableMap() {}
    const value_type *lookup(const key_type &key) const { return elts.lookup(key); }
    const value_type *lookup_previous(const key_type &key) const { return elts.lookup_previous(key); }
    ImmutableMap replace(const value_type &value) const { return elts.replace(value); }
    ImmutableMap remove(const key_type &key) const { return elts.remove(key); }
    iterator begin() const { return elts.begin(); }
    iterator end() const { return elts.end(); }
    iterator upper_bound(const key_type &key) const { return elts.upper_bound(key); }
  };
}
#endif
