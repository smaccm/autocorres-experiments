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

llnode * insert(llnode * insert, llnode * front) {
  llnode * ip = NULL;

  ip  = find_insertion(insert->val, front);
  if(front == NULL || ip == NULL) { 
    insert->next = NULL;
    return insert; 
  }
  if(insert->val == ip->val) 
  { 
    return front; 
  }
  insert->next = ip->next;
  ip->next = insert; 
  return front;
}