//
//  utils.c
//  csapp
//
//  Created by slh on 2022/2/18.
//

#include "utils.h"


char *to_binary(unsigned x) {
    size_t w = sizeof(x) * CHAR_BIT;
    char *bits = (char *)malloc(w + 1);
    for(size_t i = 0; i < w; i++) {
        *(bits + w - i - 1) = x % 2 + 48;
        x >>= 1;
    }
    *(bits + w) = '\0';
    return bits;
}
