#include <stddef.h>

typedef struct ll {
  int val;
  struct ll * next;
} ll;

ll * find_insertion(int val, ll * it) {
  ll * last = NULL;
  while (it != NULL && it->val <= val) {
    last = it;
    it = it->next;
  }
  return last;
}

ll * insert(ll * insert, ll * front) {
  ll * ip = NULL;
  ip  = find_insertion(insert->val, front);
  if(ip == NULL) { 
    insert->next = front;
    return insert; 
  } else {
    insert->next = ip->next;
    ip->next = insert; 
    return front;
  }
}