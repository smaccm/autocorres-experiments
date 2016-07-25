#include <malloc.h>

#define NULL ((void*)0)

typedef struct llnode {
  unsigned int val;
  struct llnode * next;
} llnode;

llnode * find_insertion(unsigned int val, llnode * it) {
  llnode * last = NULL;
  while (it != NULL && it->val <= val) {
    last = it;
    it = it->next;
  }
  return last;
}

int insert(llnode * insert, llnode * front) {
  if(insert == NULL) { return 0; }
  else {
    llnode * ip = find_insertion(insert->val, front);
    if(insert->val == ip->val) { return 0; }
    else if(ip == NULL) { insert->next = front; return 1;}
    else { insert->next = ip->next; ip->next = insert; return 1;}
  }
}