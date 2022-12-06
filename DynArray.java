import java.io.Serializable;
import java.util.RandomAccess;
import java.util.Set;
import java.util.Spliterator;
import java.util.function.Consumer;
import java.util.function.Predicate;
import java.util.function.UnaryOperator;
import java.util.AbstractList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.ConcurrentModificationException;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.NoSuchElementException;
import java.util.Objects;
import java.util.Random;

/**
 * <p>
 * {@code DynArray} is a similar class to
 * {@linkplain java.util.ArrayList ArrayList},
 * in that it is an unsynchronized {@link java.util.List List}
 * implementation of a dynamic array.
 * </p>
 * 
 * <p>
 * Some exclusive features present in the {@code DynArray} class include
 * the ability to: set an <i>internal comparator</i> to
 * determine the equality and ordering of elements;
 * use range-based implementations of common methods instead
 * of constructing sublists;
 * and to pass an array to any method which has also
 * takes a {@linkplain Collection} as a parameter.
 * This class uses lazy-initialization and will intialize,
 * when necessary, a backing array of length 10.
 * </p>
 * 
 * <p>
 * Note: batch methods such as {@link #removeAll(Collection) removeAll}
 * are ambiguous when {@code null} is passed.
 * There are {@link #removeNulls() "null"} equivalents
 * for every batch method.
 * </p>
 * 
 * <p>
 * One large advantage of the {@code DynArray} class is that,
 * provided all elements in a list instance have been {@link #sort() sorted}
 * with the sort method of this class, or {@link #markSorted() marked as
 * sorted},
 * either a binary or combined linear and binary search algorithm
 * will be used for any lookup-dependent operation
 * (such as {@link #retainAll(Collection)},
 * or {@link #indexOf(Object)}).
 * </p>
 * 
 * Method calls which either add or change element values
 * (including {@link #resize(n)} where {@code n} is larger than {@code size()}
 * ) such as {@link #set(int, Object)}, {@link #tradeData(int, Object[])} result
 * in
 * the {@code DynArray} being automatically marked as <b>unsorted</b> if either
 * the
 * ordering of the internal comparator, or if it is {@code null},
 * the natural ordering of elements is broken.
 * There will only be ordering checks attemped on new elements if the
 * DynArray is already marked as <b>sorted</b>.
 * 
 * <p>
 * The vast majority of methods, specified by the
 * {@link java.util.List List} interface,
 * have been overloaded to operate over a given range. This is to
 * prevent the need for repeated
 * {@link #subList(int, int) Sublist} creation.
 * Several other unspecified methods are also present,
 * including: {@link #partition(int)}, {@link #tradeData(T[])},
 * {@link #sift()} and {@link #removeWhile(Predicate, int, int)}.
 * </p>
 * 
 * <p>
 * Advanced Note: unlike the {@linkplain java.util.ArrayList ArrayList} class,
 * neither increasing capacity with {@link #ensureCapacity(int)}, nor decreasing
 * it
 * with {@link #trimToSize()}, are considered structural modifications.
 * However, all other public methods that can change the size of the list are.
 * Throughout this class there is a
 * good-effort (not best-effort) principle to check for structural modification
 * during the execution of methods that iterate over the list.
 * When found, a {@code ConcurrentModificationException} is thrown
 * </p>
 * 
 * @param <E> the type of elements in this DynArray
 * @author Antonio Oladuti
 * @see java.util.ArrayList
 * @see java.util.List
 * @see java.util.Collection
 */
public class DynArray<E> extends AbstractList<E> implements Serializable, Cloneable, RandomAccess {
    transient int modCount;
    transient protected E[] elementData;
    transient protected int capacity;
    protected int size;
    private double capacityIncrement = 2;
    private boolean growsAdditively = false;
    protected boolean isSorted = false;
    protected boolean batchSorting = false;
    protected Comparator<? super E> comparator = null;
    private static final long serialVersionUID = 8683452581122892189L;
    private static final int LAZY_INIT_CAPACITY = 10;

    @java.io.Serial
    private void writeObject(java.io.ObjectOutputStream out) throws java.io.IOException {
        out.defaultWriteObject();
        int expectedModCount = modCount;
        for (int i = 0; i < size; i++) {
            out.writeObject(elementData[i]);
        }
        out.flush();
        checkForComodification(expectedModCount);
    }

    @java.io.Serial
    @SuppressWarnings("unchecked")
    private void readObject(java.io.ObjectInputStream in)
            throws java.io.IOException, ClassNotFoundException {
        int expectedModCount = modCount;
        in.defaultReadObject();
        capacity = size; // for homogeneity with clone... size = capacity
        elementData = (E[]) new Object[capacity];
        for (int i = 0; i < size; i++) {
            elementData[i] = (E) in.readObject();
        }
        checkForComodification(expectedModCount);
    }

    // All constructors leave modCount at 0;
    @SuppressWarnings("unchecked")
    public DynArray() {
        elementData = (E[]) new Object[0];
        this.capacity = 0;
        this.size = 0;
    }

    /**
     * Constructs an empty list with the specified initial capacity.
     *
     * @param initialCapacity the initial capacity of the list
     * @throws IllegalArgumentException if the specified initial capacity
     *                                  is negative
     */
    @SuppressWarnings("unchecked")
    public DynArray(int initialCapacity) {
        elementData = (E[]) new Object[initialCapacity];
        this.capacity = elementData.length;
        this.size = 0;
    }

    /**
     * Constructs an empty list with the specified initial capacity
     * and either a multiplicative or additive capacity increment.
     * That is to say, if {@code trueSize} is the size of the backing array,
     * when the backing array is full and an element is added it will grow
     * to be the size {@code capacityIncrement * trueSize} or
     * {@code capacityIncrement + trueSize}.
     *
     * @param initialCapacity   the initial capacity of the list
     * @param capacityIncrement the increment to increase list capacity by
     * @throws IllegalArgumentException if the specified initial capacity
     *                                  is negative, or the increment is less than 1
     */
    @SuppressWarnings("unchecked")
    public DynArray(int initialCapacity, int capacityIncrement, boolean growAdditively) {
        capacityIncrementCheck(capacityIncrement);
        capacityCheck(initialCapacity);
        elementData = (E[]) new Object[initialCapacity];
        this.capacityIncrement = capacityIncrement;
        this.growsAdditively = growAdditively;
        this.capacity = elementData.length;
        this.size = 0;
    }

    /**
     * Constructs a list containing the elements of the specified
     * (non-{@code null}) array in index order
     *
     * @param a the array whose elements are to be placed into this list
     */
    @SuppressWarnings("unchecked")
    public DynArray(E[] a) {
        this.capacity = a.length;
        this.size = capacity;
        this.elementData = (E[]) new Object[capacity];
        for (int i = 0; i < a.length; i++) {
            this.elementData[i] = a[i];
        }
        if (size > 0)
            isSorted = checkSorting(0, size);
    }

    @SuppressWarnings("unchecked")
    public DynArray(Collection<? extends E> c) {
        size = capacity = c.size();
        elementData = (E[]) new Object[capacity];
        if (capacity > 0) {
            int i = 0;
            for (E e : c) {
                elementData[i] = e;
                i++;
            }
        }
        if (size > 0)
            isSorted = checkSorting(0, size);
    }

    /**
     * @throws IndexOutOfBoundsException {@inheritDoc}
     */
    @Override
    public E get(int index) {
        indexCheck(index);
        return elementData[index];
    }

    private void checkComparator(Comparator<? super E> c) {
        if (c != null && c != comparator) {
            if (c.equals(comparator))
                return;
            if (size > 1) {
                c.compare(elementData[0], elementData[1]);
            }
        }
    }

    /**
     * Returns the internal comparator for this {@code DynArray} instance.
     * 
     * @return the internal comparator for this {@code DynArray} instance
     */
    public Comparator<? super E> getComparator() {
        return comparator;
    }

    /**
     * Sets the internal comparator for this {@code DynArray} instance,
     * to be used in all lookup-dependent or sorting methods.
     * 
     * Note: if this {@code DynArray} instance contains null elements,
     * {@code comparator} must be able to compare to {@code null}.
     * 
     * @param comparator the new comparator
     */
    public void setComparator(Comparator<? super E> comparator) {
        checkComparator(comparator);
        this.comparator = comparator;
    }

    /**
     * Returns true if this list is marked as <b>sorted</b>.
     * 
     * @return true if this list is marked as <b>sorted</b>
     */
    public boolean isSorted() {
        return isSorted;
    }

    /** Marks this {@code DynArray} instance as <b>sorted</b> **/
    public void markSorted() {
        isSorted = true;
    }

    @Override
    public int size() {
        return (size > Integer.MAX_VALUE) ? Integer.MAX_VALUE : size;
    }

    @Override
    public boolean isEmpty() {
        return size == 0;
    }

    /**
     * Returns {@code true} if this {@code DynArray} contains the specified element.
     * More formally, returns {@code true} if this {@code DynArray}
     * contains at least one element {@code e} such that
     * {@code Objects.equals(o, e)} or the
     * <i>internal comparator</i> method {@code compare(o, e) == 0}.
     *
     * @param o element whose presence in this {@code DynArray} is to be tested
     * @return {@code true} if this {@code DynArray} contains the specified
     *         element
     * @throws ClassCastException if the type of the specified element
     *                            is incompatible with this {@code DynArray}
     */
    @Override
    @SuppressWarnings("unchecked")
    public boolean contains(Object o) {
        return anyIndexOf(0, size, (E) o) != -1; // early cast for fast-failure
    }

    /**
     * @throws NullPointerException {@inheritDoc}
     */
    @Override
    public void forEach(Consumer<? super E> action) {
        Objects.requireNonNull(action);
        int expectedModCount = modCount;
        for (int i = 0; i < size; i++) {
            action.accept(elementData[i]);
            if (i == 0)
                checkForComodification(expectedModCount); // avoiding repeated checks
        }
    }

    /**
     * <p>
     * Returns an unmodifiable list view containing a specific number of consecutive
     * {@code DynArray} {@link #subList(int, int) sublists},
     * each of the <b>same</b> size (the final list may be smaller
     * if {@code withPadding} is {@code false}). <br />
     * However, if {@code withPadding} is {@code true} and
     * {@code DynArray.size() % numberOfParts != 0},
     * the final sublist will be padded by trailing {@code null} elements
     * to ensure <b> all </b> sublists are the same size.
     * </p>
     * 
     * <p>
     * For instance, partitioning a list containing [a, b, c, d, e]
     * with {@code numberOfParts} set to 2 and {@code withPadding} set to
     * {@code true}
     * yields [[a, b, c], [d, e, null]]
     * -- an outer list containing two inner lists of three elements each,
     * all in the original order.
     * </p>
     * 
     * The inner lists are sublist views of the original list,
     * produced on demand using {@link#subList(int,int)},
     * and are subject to all the usual caveats of {@code DynArray} sublists.
     * If {@code withPadding} is true, and {@code null}-padding is required,
     * then the final sublist in the outer list will <b>not</b> be
     * a view of this {@code DynArray} instance.
     * 
     * @param numberOfParts the desired number of sublists
     * @param withPadding   if {@code true} then,
     *                      if {@code DynArray.size() % numberOfParts != 0},
     *                      the final sublist returned will be padded by trailing
     *                      {@code null} elements
     * @throws IllegalArgumentException if {@code numberOfParts} <= 0
     *                                  or {@code numberOfParts} >
     *                                  {@code DynArray.size()}
     * @return an unmodifiable list of consecutive sublists
     */
    public List<List<E>> fixedPartition(int numberOfParts, boolean withPadding) {
        if (numberOfParts <= 0 || numberOfParts > this.size)
            throw new IllegalArgumentException();
        if (this.size == 0)
            return new DynArray<>();
        int partSize = this.size / numberOfParts;
        DynArray<DynArray<E>> list = new DynArray<>(numberOfParts);
        int i = 0;
        int pad = this.size % numberOfParts;
        while (i < numberOfParts - 1) {
            // Pad is used here before branching to:
            // 1. ensure that only the final SubList is smaller even if withPadding is false
            // 2. Allow padding to work if it is enabled
            list.add((DynArray<E>) subList(i * partSize, (i * partSize) + partSize + pad));
            i++;
        }
        if (!withPadding || pad == 0) {
            list.add((DynArray<E>) subList(i * partSize + pad, this.size));
        } else {
            DynArray<E> finale = new DynArray<E>();
            if (i * partSize != this.size) {
                finale.addAll(this.subList(i * partSize + pad, this.size));
                for (int j = finale.size(); j < partSize + pad; j++) {
                    finale.add(null);
                }
                list.add(finale);
            }
        }
        return Collections.unmodifiableList(list);
    }

    /**
     * <p>
     * Returns an immutable list view containing consecutive
     * {@code DynArray} {@link #subList(int, int) sublists},
     * each of the same size (the final list may be smaller
     * if {@code withPadding} is {@code false}). <br />
     * However, if {@code withPadding} is {@code true} and
     * {@code DynArray.size() % partSize != 0},
     * the final sublist will be padded by trailing {@code null} elements
     * to ensure <b> all </b> sublists are the same size.
     * </p>
     * 
     * For instance, partitioning a list containing
     * [x, y, z] with {@code partSize} set to 2 and
     * {@code withPadding} set to {@code false} yields
     * [ [x, y], [z] ] -- an outer list containing two inner
     * lists of with two elements in the first,
     * and one element in the second, all in the original order.
     * </p>
     *
     * The inner lists are sublist views of the original list,
     * produced on demand using {@link#subList(int,int)},
     * and are subject to all the usual caveats of {@code DynArray} sublists.
     * If {@code withPadding} is true, and {@code null}-padding is required,
     * then the final sublist in the outer list will <b>not</b> be
     * a view of this {@code DynArray} instance.
     * 
     * @param partSize    the desired size of the sublists
     * @param withPadding if {@code true} then,
     *                    if {@code DynArray.size() % partSize != 0},
     *                    the final sublist returned will be padded by trailing
     *                    {@code null} elements
     * @return an unmodifiable list of consecutive sublists
     * @throws IllegalArgumentException if {@code partsize <= 0}
     */
    public List<List<E>> partition(int partSize, boolean withPadding) {
        if (partSize <= 0)
            throw new IllegalArgumentException();
        if (withPadding && (this.size % partSize == 0))
            withPadding = false;
        if (this.size == 0)
            return new DynArray<>();
        DynArray<DynArray<E>> list = new DynArray<>(this.size / partSize);
        int i = 0;
        while (i * partSize + partSize < this.size) {
            list.add((DynArray<E>) subList(i * partSize, (i * partSize) + partSize));
            i++;
        }
        if (!withPadding) {
            list.add((DynArray<E>) subList(i * partSize, this.size));
        } else {
            DynArray<E> finale = new DynArray<E>();
            if (i * partSize != this.size) {
                finale.addAll(this.subList(i * partSize, this.size));
                for (int j = finale.size(); j < partSize; j++) {
                    finale.add(null);
                }
                list.add(finale);
            }
        }
        return Collections.unmodifiableList(list);
    }

    @Override
    public Iterator<E> iterator() {
        return new Itr();
    }

    class Itr implements Iterator<E> {
        protected int i = -1;
        protected int lastRet = -1;
        protected int expectedModCount = modCount;

        @Override
        public boolean hasNext() {
            return (i < size - 1);
        }

        @Override
        public E next() {
            checkForComodification();
            i++;
            lastRet = i;
            if (i >= size)
                throw new NoSuchElementException();
            if (i >= elementData.length)
                throw new ConcurrentModificationException();
            return elementData[i];
        }

        public void remove() {
            checkForComodification();
            if (lastRet == -1)
                throw new IllegalStateException();
            try {
                DynArray.this.remove(lastRet);
                expectedModCount++;
                i--;
            } catch (IndexOutOfBoundsException ex) {
                throw new ConcurrentModificationException();
            }
        }

        @Override
        public void forEachRemaining(Consumer<? super E> c) {
            final Object[] itData = elementData;
            if (i > itData.length)
                throw new ConcurrentModificationException();
            for (final int itSize = size; i < itSize && modCount == expectedModCount; i++)
                c.accept(elementData[i]);
            checkForComodification();
        }

        protected void checkForComodification() {
            if (modCount != expectedModCount)
                throw new ConcurrentModificationException();
        }
    }

    @Override
    public Object[] toArray() {
        Object[] partial = new Object[size];
        for (int i = 0; i < size; i++) {
            partial[i] = elementData[i];
        }
        return partial;
    }

    /**
     * Returns an array containing all of the elements in this list in proper
     * sequence (from first to last element); the runtime type of the returned
     * array is that of the specified array. If the list fits in the
     * specified array, it is returned therein. Otherwise, a new array is
     * allocated with the runtime type of the specified array and the size of
     * this list.
     *
     * <p>
     * If the list fits in the specified array with room to spare
     * (i.e., the array has more elements than the list), the element in
     * the array immediately following the end of the collection is set to
     * {@code null}. (This is useful in determining the length of the
     * list <i>only</i> if the caller knows that the list does not contain
     * any null elements.)
     *
     * @param a the array into which the elements of the list are to
     *          be stored, if it is big enough; otherwise, a new array of the
     *          same runtime type is allocated for this purpose.
     * @return an array containing the elements of the list
     * @throws ArrayStoreException  if the runtime type of the specified array
     *                              is not a supertype of the runtime type of every
     *                              element in
     *                              this list
     * @throws NullPointerException if the specified array is null
     */
    @SuppressWarnings("unchecked")
    public <T> T[] toArray(T[] a) {
        if (a.length < size)
            // Make a new array of a's runtime type, but my contents:
            return (T[]) Arrays.copyOf(elementData, size, a.getClass());
        System.arraycopy(elementData, 0, a, 0, size);
        if (a.length > size)
            a[size] = null;
        return a;
    }

    /**
     * Appends the specified element to the end of this list.
     *
     * @param e element to be appended to this list
     * @return {@code true} (as specified by {@link Collection#add})
     */
    public boolean add(E e) {
        resize0(size + 1);
        elementData[size - 1] = e;
        isSorted = checkSorting(size - 2, size);
        return true;
    }

    /**
     * Inserts the specified element at the specified position in this
     * list. Shifts the element currently at that position (if any) and
     * any subsequent elements to the right (adds one to their indices).
     * This list is marked as <b>unsorted</b> as a result of the call.
     *
     * @param index   index at which the specified element is to be inserted
     * @param element element to be inserted
     * @throws IndexOutOfBoundsException {@inheritDoc}
     */
    @Override
    public void add(int index, E element) {
        addIndexCheck(index);
        resize0(size + 1);
        for (int i = size - 1; i > index; i--) {
            elementData[i] = elementData[i - 1];
        }
        elementData[index] = element;
        isSorted = checkSorting(index, index + 2);
    }

    /**
     * Removes the first occurrence of the specified element from this list,
     * if it is present. If the list does not contain the element, it is
     * unchanged. More formally, removes the element with the lowest
     * index {@code i} such that {@code Objects.equals(o, get(i))}
     * or {@code getComparator().compare(o, get(i)) == 0}
     * (if this list has an internal comparator).
     * Returns {@code true} if this list
     * contained the specified element (or equivalently, if this list
     * changed as a result of the call).
     *
     * @param o element to be removed from this list, if present
     * @return {@code true} if this list contained the specified element
     */
    @Override
    public boolean remove(Object o) {
        return remove(0, size, o);
    }

    /**
     * Removes the first occurrence of the specified element in the
     * specified range of this list, if it is present.
     * If the range does not contain the element, it is
     * unchanged. More formally, removes the element in range with the lowest
     * index {@code i} such that {@code Objects.equals(o, get(i))}
     * or {@code getComparator().compare(o, get(i)) == 0}
     * (if this list has an internal comparator).
     * Returns {@code true} if the range
     * contained the specified element (or equivalently, if this list
     * changed as a result of the call).
     * 
     * @param fromIndex the index of the first element (inclusive) to be
     *                  searched
     * @param toIndex   the index of the last element (exclusive) to be searched
     * @param o         element to be removed from this list, if present
     * @return {@code true} if this list contained the specified element
     */
    public boolean remove(int fromIndex, int toIndex, Object o) {
        int firstIndex = indexOf(fromIndex, toIndex, o);
        if (firstIndex != -1) {
            eraseAndMod(firstIndex);
            return true;
        }
        return false;
    }

    /**
     * {@inheritDoc}
     * 
     * @throws ClassCastException if the type of one or more elements in the
     *                            in the specified collection are incompatible with
     *                            this {@code DynArray}
     * @see #contains(Object)
     */
    @Override
    public boolean containsAll(Collection<?> c) {
        ;
        return super.containsAll(c);
    }

    /**
     * Returns {@code true} if this list contains all elements in the specified
     * array.
     * 
     * @param a array to be checked for containment in this list
     * @return {@code true} if this list contains all elements in the specified
     *         array
     * @throws ClassCastException if the type of one or more elements in the
     *                            in the specified collection are incompatible with
     *                            this {@code DynArray}
     * @see #contains(Object)
     */
    public boolean containsAll(Object[] a) {
        boolean containsItems = false;
        for (int i = 0; i < a.length; i++) {
            containsItems = (anyIndexOf(0, size, a[i]) != -1);
            if (!containsItems)
                break;
        }
        return containsItems;
    }

    /**
     * When {@code enabled} is set to {@code true},
     * a call to any {@code AddAll()} method will
     * call {@link #sort()} on this {@code DynArray}
     * instance.
     * 
     * @param enabled turns sorting on when true
     */
    public void enableSortOnAddAll(boolean enabled) {
        batchSorting = enabled;
    }

    /**
     * <p>
     * Appends all of the elements in the specified collection to the end of
     * this list, in the order that they are returned by the
     * specified collection's Iterator. The behavior of this operation is
     * undefined if the specified collection is modified while the operation
     * is in progress. (This implies that the behavior of this call is
     * undefined if the specified collection is this list, and this
     * list is nonempty.)
     * </p>
     * 
     * If this list changed as a result
     * of the call, it is also marked as <b>unsorted</b>.
     *
     * @param c collection containing elements to be added to this list
     * @return {@code true} if this list changed as a result of the call
     */
    @Override
    public boolean addAll(Collection<? extends E> c) {
        int start = size;
        if (c != this) {
            if (c == null)
                return false;
            resize0(size + c.size());
            for (E e : c) {
                elementData[start] = e;
                start++;
            }
            if (batchSorting) {
                sort();
            } else {
                isSorted = checkSorting(size - c.size() - 1, size);
            }
            return true;
        } else {
            @SuppressWarnings("unchecked")
            E[] elDa = (E[]) new Object[size];
            for (int i = 0; i < size; i++) {
                elDa[i] = elementData[i];
            }
            return addAll(elDa);
        }
    }

    /**
     * <p>
     * Appends all of the elements in the specified array to the end of
     * this list, in ascending array index order.
     * The behavior of this operation is
     * undefined if the specified array is modified while the operation
     * is in progress.
     * </p>
     * 
     * If this list changed as a result
     * of the call, it is also marked as <b>unsorted</b>.
     *
     * @param a array containing elements to be added to this list
     * @return {@code true} if this list changed as a result of the call
     */
    public boolean addAll(E[] a) {
        if (a == null)
            return false;
        int index = size;
        resize0(size + a.length);
        for (int i = 0; i < a.length; i++) {
            elementData[index + i] = a[i];
        }
        if (batchSorting) {
            sort();
        } else {
            isSorted = checkSorting(size - a.length - 1, size);
        }
        return true;
    }

    /**
     * <p>
     * Inserts all of the elements in the array into this
     * list at the specified position. Shifts the
     * element currently at that position (if any) and any subsequent
     * elements to the right (increases their indices). The new elements
     * will appear in this list in ascending index order of the specified array.
     * The behavior of this operation is
     * undefined if the specified array is modified while the
     * operation is in progress.
     * </p>
     * 
     * If this list changed as a result
     * of the call, it is also marked as <b>unsorted</b>.
     *
     * @param index index at which to insert the first element from the
     *              specified array
     * @param a     array containing elements to be added to this list
     * @return {@code true} if this list changed as a result of the call
     */
    public boolean addAll(int index, E[] a) {
        addIndexCheck(index);
        resize0(size + a.length);
        for (int i = size - 1; i > index + a.length - 1; i--) {
            elementData[i] = elementData[i - a.length];
        }
        for (int i = 0; i < a.length; i++) {
            elementData[index + i] = a[i];
        }
        if (batchSorting) {
            sort();
        } else {
            isSorted = checkSorting(index, index + a.length + 1);
        }
        return true;
    }

    /**
     * Removes from this list all of its elements that are contained in the
     * specified collection.
     *
     * @param c collection containing elements to be removed from this list
     * @return {@code true} if this list changed as a result of the call
     * @see #contains(Object)
     */
    @Override
    public boolean removeAll(Collection<?> c) {
        return removeAll(0, size, c);
    }

    /**
     * Removes from the specified range of this list all elements
     * that are contained in the
     * specified collection.
     *
     * @param c         collection containing elements to be removed from this list
     * @param fromIndex the index of the first element in the range (inclusive)
     * @param toIndex   the index of the last element in the range (exclusive)
     * @return {@code true} if this list changed as a result of the call
     * @see #contains(Object)
     */
    public boolean removeAll(int fromIndex, int toIndex, Collection<?> c) {
        boolean changed = false;
        if (c != this) {
            for (Object o : c) {
                for (int index = indexOf(fromIndex, toIndex, o); index != -1; index = linearIndexOf(index, toIndex,
                        o)) {
                    erase(index);
                    changed = checkChange(changed);
                }
            }
        } else {
            if (size != 0)
                changed = true;
            clear();
        }
        return changed;
    }

    /**
     * Removes from this list all of its elements that are contained in the
     * specified array.
     *
     * @param a array containing elements to be removed from this list
     * @return {@code true} if this list changed as a result of the call
     */
    public boolean removeAll(Object[] a) {
        return removeAll(0, size, a);
    }

    /**
     * Removes from the specified range of this list all elements
     * that are contained in the
     * specified array.
     *
     * @param a         array containing elements to be removed from this list
     * @param fromIndex the index of the first element in the range (inclusive)
     * @param toIndex   the index of the last element in the range (exclusive)
     * @return {@code true} if this list changed as a result of the call
     * @see #contains(Object)
     */
    public boolean removeAll(int fromIndex, int toIndex, Object[] a) {
        boolean changed = false;
        for (int i = 0; i < a.length; i++) {
            for (int index = indexOf(fromIndex, toIndex, a[i]); index != -1; index = linearIndexOf(index, toIndex,
                    a[i])) {
                erase(index);
                changed = checkChange(changed);
            }
        }
        return changed;
    }

    /**
     * Removes all occurrences of the specified element from this list,
     * if it is present. If the list does not contain the element, it is
     * unchanged. More formally, removes all elements at any
     * index {@code i} such that either {@code Objects.equals(o, get(i))}
     * or {@code getComparator().compare(o, get(i)) == 0}
     * (if this list has an internal comparator).
     * Returns {@code true} if this list
     * contained the specified element (or equivalently, if this list
     * changed as a result of the call).
     *
     * @param o element to be removed from this list, if present
     * @return {@code true} if this list contained the specified element
     */
    public boolean removeAll(Object o) {
        return remove(0, size, o);
    }

    /**
     * Removes all occurrences of the specified element in the
     * specified range of this list, if it is present.
     * If the range does not contain the element, it is
     * unchanged. More formally, removes all elements at any index {@code i}
     * in the range such that either {@code Objects.equals(o, get(i))}
     * or {@code getComparator().compare(o, get(i)) == 0}
     * (if this list has an internal comparator).
     * Returns {@code true} if the range
     * contained the specified element (or equivalently, if this list
     * changed as a result of the call).
     * 
     * @param fromIndex the index of the first element in the range (inclusive)
     * @param toIndex   the index of the last element in the range (exclusive)
     * @param o         element to be removed from the range, if present
     * @return {@code true} if the range contained the specified element
     */
    public boolean removeAll(int fromIndex, int toIndex, Object o) {
        boolean changed = false;
        for (int index = indexOf(fromIndex, toIndex, o); index != -1; index = linearIndexOf(index, toIndex, o)) {
            erase(index);
            changed = checkChange(changed);
        }
        return changed;
    }

    /**
     * Retains only the elements in this list that are contained in the
     * specified collection. In other words, removes from this list all
     * of its elements that are not contained in the specified collection.
     * 
     * @param c collection containing elements to be retained in this list
     * @return {@code true} if this list changed as a result of the call
     * 
     * @see #remove(Object)
     * @see #contains(Object)
     */
    @Override
    public boolean retainAll(Collection<?> c) {
        return retainAll(0, size, c);
    }

    /**
     * Retains, in the specified range of this list, only the elements
     * that are contained in the specified collection.
     * In other words, removes from the range all
     * of its elements that are not contained in the specified collection.
     * 
     * @param c         collection containing elements to be retained in this list
     * @param fromIndex the index of the first element (inclusive) to be
     *                  searched for in {@code c}
     * @param toIndex   the index of the last element (exclusive) to be
     *                  searched for in {@code c}
     * @return {@code true} if this list changed as a result of the call
     * 
     * @see #remove(Object)
     * @see #contains(Object)
     */
    @SuppressWarnings("unchecked")
    public boolean retainAll(int fromIndex, int toIndex, Collection<?> c) {
        // no null-check since
        rangeCheck(fromIndex, toIndex);
        boolean changed = false;
        for (int i = 0, j = fromIndex; i < toIndex - fromIndex; i++) {
            int count = 0;
            for (Object o : c) {
                if (elementData[j] == null || o == null) {
                    if (elementData[j] == o)
                        count++;
                } else if (comparator == null) {
                    if (elementData[j].equals(o))
                        count++;
                } else if (comparator.compare(elementData[j], (E) o) == 0) {
                    count++;
                }
                if (count > 0)
                    break;
            }
            if (count == 0) {
                erase(j);
                j--;
                changed = checkChange(changed);
            }
            j++;
        }
        return changed;
    }

    /**
     * Retains only {@code null} elements of this list.
     * In other words, removes from this list all elements that are not
     * {@code null}.
     * 
     * @return {@code true} if this list changed as a result of the call
     * 
     */
    public boolean retainNulls() {
        return retainNulls(0, this.size);
    }

    /**
     * Retains only {@code null} elements in the specified range of this list.
     * In other words, removes from the range all elements that are not
     * {@code null}.
     * 
     * @param fromIndex the index of the first element in the range (inclusive)
     * @param toIndex   the index of the last element in the range (exclusive)
     * @return {@code true} if this list changed as a result of the call
     * 
     */
    public boolean retainNulls(int fromIndex, int toIndex) {
        rangeCheck(fromIndex, toIndex);
        boolean changed = false;
        for (int i = 0, j = fromIndex; i < toIndex - fromIndex; i++) {
            boolean del = false;
            if (!(elementData[j] == null))
                del = true;
            if (del == true) {
                erase(j);
                j--;
                changed = checkChange(changed);
            }
            j++;
        }
        return changed;
    }

    /**
     * Retains only the elements in this list that are contained in the
     * specified array. In other words, removes from this list all
     * of its elements that are not contained in the specified array.
     * 
     * @param a array containing elements to be retained in this list
     * @return {@code true} if this list changed as a result of the call
     * 
     * @see #remove(Object)
     * @see #contains(Object)
     */
    public boolean retainAll(Object[] a) {
        return retainAll(0, size, a);
    }

    /**
     * Retains, in the specified range of this list, only the elements
     * that are contained in the
     * specified array. In other words, removes from the range all
     * of its elements that are not contained in the specified array.
     * 
     * @param a         array containing elements to be retained in this list
     * @param fromIndex the index of the first element (inclusive) to be
     *                  searched for in {@code a}
     * @param toIndex   the index of the last element (exclusive) to be
     *                  searched for in {@code a}
     * @return {@code true} if this list changed as a result of the call
     * 
     * @see #remove(Object)
     * @see #contains(Object)
     */
    @SuppressWarnings("unchecked")
    public boolean retainAll(int fromIndex, int toIndex, Object[] a) {
        rangeCheck(fromIndex, toIndex);
        boolean changed = false;
        for (int i = 0, j = fromIndex; i < toIndex - fromIndex; i++) {
            int count = 0;
            for (int o = 0; o < a.length; o++) {
                if ((elementData[j] == null || a[o] == null)) {
                    if (elementData[j] == a[o])
                        count++;
                } else if (comparator == null) {
                    if (elementData[j].equals(a[o]))
                        count++;
                } else if (comparator.compare(elementData[j], (E) a[o]) == 0) {
                    count++;
                }
                if (count > 0)
                    break;
            }
            if (count == 0) {
                erase(j);
                j--;
                changed = checkChange(changed);
            }
            j++;
        }
        return changed;
    }

    /**
     * Retains, in the specified range of this list,
     * only the elements that are equal to {@code o}.
     * More formally, removes all elements at any
     * index {@code i} such that either
     * {@code !(getComparator().compare(o, get(i)) == 0)} (if this list
     * has an internal comparator)
     * or secondarily {@code !Objects.equals(o, get(i))}.
     * 
     * @param o element to retain
     * @return {@code true} if this list changed as a result of the call
     * 
     * @see #remove(Object)
     * @see #contains(Object)
     */
    public boolean retainAll(Object o) {
        return retainAll(0, size, o);
    }

    /**
     * Retains only the elements in this list that are equal to {@code o}.
     * More formally, removes all elements at any
     * index {@code i} in range such that either
     * {@code !(getComparator().compare(o, get(i)) == 0)} (if this list
     * has an internal comparator)
     * or secondarily {@code !Objects.equals(o, get(i))}.
     * 
     * @param o         element to retain
     * @param fromIndex the index of the first element (inclusive) to be
     *                  retained
     * @param toIndex   the index of the last element (exclusive) to be
     *                  retained
     * @return {@code true} if this list changed as a result of the call
     * 
     * @see #remove(Object)
     * @see #contains(Object)
     */
    @SuppressWarnings("unchecked")
    public boolean retainAll(int fromIndex, int toIndex, Object o) {
        rangeCheck(fromIndex, toIndex);
        boolean changed = false;
        for (int i = fromIndex, j = fromIndex; i < toIndex - fromIndex; i++) {
            boolean mustErase = false;
            if (comparator != null && (comparator.compare(elementData[j], (E) o) != 0)) {
                mustErase = true;
            } else if ((elementData[j] == null || o == null)) {
                if (elementData[j] != o)
                    mustErase = true;
            } else if (!elementData[j].equals(o)) {
                mustErase = true;
            }
            if (mustErase) {
                erase(j);
                j--;
                changed = checkChange(changed);
            }
            j++;
        }
        return changed;
    }

    /**
     * Returns true if this {@code DynArray} instance contains
     * at least one {@code null} element.
     * 
     * @return true if this {@code DynArray} instance contains
     *         at least one {@code null} element
     */
    public boolean containsNulls() {
        for (int i = 0; i < size; i++) {
            if (elementData[i] == null)
                return true;
        }
        return false;
    }

    /**
     * Sets the internal comparator to the {@code c}
     * and sorts this list according to the order induced by it.
     * The sort is <i>stable</i>: this method must not
     * reorder equal elements.
     *
     * <p>
     * All elements in this list must be <i>mutually comparable</i> using the
     * specified {@link Comparator} (that is, {@code c.compare(e1, e2)} must not
     * throw
     * a {@code ClassCastException} for any elements {@code e1} and {@code e2}
     * in the list).
     *
     * <p>
     * If the specified comparator is {@code null} then all elements in this
     * list must implement the {@link Comparable} interface and the elements'
     * {@linkplain Comparable natural ordering} should be used.
     *
     *
     * @param c the {@code Comparator} used to compare list elements.
     *          A {@code null} value indicates that the elements'
     *          {@linkplain Comparable natural ordering} should be used
     * @throws ClassCastException if the list contains elements that are not
     *                            <i>mutually comparable</i> using the specified
     *                            comparator
     */
    @Override
    public void sort(Comparator<? super E> c) {
        checkComparator(c);
        Arrays.sort(elementData, 0, size, c);
        isSorted = true;
    }

    // Sorts without checking DynArray elementData -- fast
    public void sort() {
        if (comparator != null) {
            sort(comparator);
            return;
        }
        Arrays.sort(elementData, 0, size);
        isSorted = true;
    }

    /**
     * Removes all {@code null} elements from this list.
     * 
     * @return {@code true} if a {@code null} element was removed
     */
    public boolean removeNulls() {
        int[] result = indicesOf(null);
        if (result.length == 0)
            return false;
        for (int i = 0; i < result.length; i++) {
            erase(result[i] - i);
        }
        modCount++;
        return true;
    }

    /**
     * Removes all {@code null} elements from this list in range.
     * 
     * @return {@code true} if a {@code null} element was removed
     */
    public boolean removeNulls(int fromIndex, int toIndex) {
        rangeCheck(fromIndex, toIndex);
        for (int i = 0, lim = toIndex; i < lim; i++) {
            if (elementData[i] == null) {
                erase(i);
                lim--;
                i--;
            }
        }
        modCount++;
        return true;
    }

    /**
     * Searches this {@code DynArray} using the
     * {@link java.util.Arrays Arrays} class binary search algorithm.
     * If the <i>internal comparator</i> is <b>not</b> {@code null},
     * it will be used to compare elements,
     * otherwise the {@linkplain Comparable natural ordering}
     * of elements will be used.
     * The data must be sorted into ascending order
     * (as by the {@link #sort(int, int) sort(int, int)}
     * method) prior to making this call.
     * If the data not sorted, the results are undefined.
     * If the data contains multiple elements equal to the specified object,
     * there is no guarantee which one will be found.
     *
     * @param key the value to be searched for
     * @return index of the search key, if it is contained in the {@code DynArray}
     *         within the specified range;
     *         otherwise, <code>(-(<i>insertion point</i>) - 1)</code>. The
     *         <i>insertion point</i> is defined as the point at which the
     *         key would be inserted into this list: the index of the first
     *         element in this list greater than the key,
     *         or {@code size} if all
     *         elements in the range are less than the specified key. Note
     *         that this guarantees that the return value will be &gt;= 0 if
     *         and only if the key is found.
     * @throws ClassCastException   if this list contains elements that are not
     *                              <i>mutually comparable</i> using its comparator;
     *                              the search key is not comparable to the
     *                              elements in this list using its comparator; or,
     *                              if this list has no
     *                              comparator, at least one
     *                              {@code DynArray} element does not implement the
     *                              {@linkplain Comparable} interface.
     * @throws NullPointerException if any element in this list is {@code null},
     *                              and this list either has no comparator or
     *                              its comparator does not permit
     *                              {@code null} elements.
     */
    public int binarySearch(E key) {
        return Arrays.binarySearch(elementData, 0, size, key, comparator);
    }

    /**
     * Searches a range of this {@code DynArray} using the
     * {@link java.util.Arrays Arrays} class binary search algorithm.
     * If the internal comparator is <b>not</b> {@code null},
     * it will be used to compare elements,
     * otherwise the {@linkplain Comparable natural ordering}
     * of elements will be used.
     * The range must be sorted into ascending order
     * (as by the {@link #sort(int, int) sort(int, int)}
     * method) prior to making this call.
     * If the range is not sorted, the results are undefined.
     * And, if the range contains multiple elements equal to the specified object,
     * there is no guarantee which one will be found.
     *
     * @param fromIndex the index of the first element (inclusive) to be
     *                  searched
     * @param toIndex   the index of the last element (exclusive) to be searched
     * @param key       the value to be searched for
     * @return index of the search key, if it is contained in the DynArray
     *         within the specified range;
     *         otherwise, <code>(-(<i>insertion point</i>) - 1)</code>. The
     *         <i>insertion point</i> is defined as the point at which the
     *         key would be inserted into this list: the index of the first
     *         element in the range greater than the key,
     *         or {@code toIndex} if all
     *         elements in the range are less than the specified key. Note
     *         that this guarantees that the return value will be &gt;= 0 if
     *         and only if the key is found.
     * @throws ClassCastException   if either: the range contains elements that are
     *                              not
     *                              <i>mutually comparable</i> using this list's
     *                              comparator;
     *                              the search key is not comparable to the
     *                              elements in this list using its comparator; or,
     *                              if there is no
     *                              comparator, at least one
     *                              {@code DynArray} element does not implement the
     *                              {@linkplain Comparable} interface.
     * @throws NullPointerException if any element in the range is {@code null},
     *                              and this list either has no comparator or
     *                              its comparator does not permit
     *                              {@code null} elements.
     */
    public int binarySearch(int fromIndex, int toIndex, E key) {
        rangeCheck(fromIndex, toIndex);
        return Arrays.binarySearch(elementData, fromIndex, toIndex, key, comparator);
    }

    /**
     * Swaps round the element at index {@code i} with the
     * element at index {@code j} in this list. If this
     * {@code DynArray} instance becomes unsorted as a result
     * of the call it is marked as <b>unsorted</b>.
     * 
     * @param i index of the element to be swapped with
     *          the element at index {@code j}
     * @param j index of the element to be swapped
     *          with the element at index {@code i}
     */
    public void swap(int i, int j) {
        indexCheck(i);
        indexCheck(j);
        E switcheroo = elementData[i];
        elementData[i] = elementData[j];
        elementData[j] = switcheroo;
        isSorted = checkSorting(i, i + 2) && checkSorting(j, j + 2);
    }

    /**
     * Randomly shuffles round the order of elements in this
     * {@code DynArray} instance and marks it as
     * <b>unsorted</b>.
     */
    public void shuffle() {
        Random r = new Random();
        int marks[] = new int[size];
        int unmarkedBound = size;
        int startIndex = 0;
        int i = 0;
        while (i < size) {
            int switcher = r.nextInt(unmarkedBound - startIndex) + startIndex;
            if (marks[switcher] < 1) {
                marks[switcher]++;
                i++;
            }
            int switchee = r.nextInt(unmarkedBound - startIndex) + startIndex;
            if (marks[unmarkedBound - 1] > 0) {
                unmarkedBound--;
            }
            if (marks[startIndex] > 0) {
                startIndex++;
            }
            if (marks[switchee] < 1) {
                if (marks[switcher] > 0) {
                    swap(switcher, switchee);
                }
                marks[switchee]++;
                i++;
            }
        }
        isSorted = false;
    }

    @Override
    public String toString() {
        if (size == 0)
            return "[]";
        String concat = "[";
        for (int i = 0; i < size - 1; i++) {
            if (!(elementData[i] == null)) {
                concat += elementData[i].toString() + ", ";
            } else {
                concat += "null, ";
            }
        }
        ;
        if (elementData[size - 1] == null) {
            return concat + "null]";
        }
        return concat + elementData[size - 1].toString() + "]";
    }

    /**
     * <p>
     * Removes duplicates of every element from this {@code DynArray} instance,
     * and returns {@code true} if this list contained duplicate elements.
     * Duplicates are removed from the back of the list first
     * (i.e. descending index order).
     * </p>
     * 
     * More formally, for each element at index {@code i} (starting from
     * {@code i = 0}),
     * removes all equivalent elements in this list
     * at every other index {@code j}
     * (starting from the {@code j = size() - 1})
     * such that {@code getComparator().compare(get(i), get(j)) == 0}
     * (if this list has an internal comparator) or secondarily
     * {@code Objects.equals(get(i), get(j))}.
     * 
     * @return {@code true} if this list contained duplicate elements
     * @see #remove(Object)
     */
    public boolean sift() {
        boolean changed = false;
        for (int i = 0; i < size; i++) {
            int j = lastIndexOf(elementData[i]);
            while (j != indexOf(elementData[i])) {
                erase(j);
                j = lastIndexOf(elementData[i]);
                changed = checkChange(changed);
            }
            ;
        }
        return changed;
    }

    /**
     * <p>
     * Returns a {@link java.util.Set Set} containing,
     * in proper sequence (first to last), one of each distinct element in this
     * list.
     * Element distinction, if the internal comparator is not
     * {@code null}, will be determined by its
     * {@link java.util.Comparator#compare(o1, o2) compare(o1, o2)}
     * method. Otherwise, elements will be checked
     * for equality by calling their own {@code equals(o)} methods.
     * </p>
     * 
     * The returned {@code Set} will be "safe" in that
     * no references to it are maintained by this list.
     * (In other words, this method must create a new {@code DynArray}
     * to back the returned {@code Set}).
     * The caller is thus free to modify the returned {@code Set}.
     * 
     * @return a {@code Set} containing,
     *         in proper sequence, one of each
     *         distinct element in this list
     */
    @SuppressWarnings("unchecked")
    public Set<E> toSet() {
        DynArray<E> s = (DynArray<E>) clone();
        s.sift();
        Set<E> set = new Set<E>() {
            @Override
            public int size() {
                return s.size;
            }

            @Override
            public boolean isEmpty() {
                return s.size == 0;
            }

            @Override
            public boolean contains(Object o) {
                return s.contains(o);
            }

            @Override
            public Iterator<E> iterator() {
                return s.iterator();
            }

            @Override
            public Object[] toArray() {
                return s.toArray();
            }

            @Override
            public <T> T[] toArray(T[] a) {
                return s.toArray(a);
            }

            @Override
            public boolean add(E e) {
                return isPresent(e) ? s.add(e) : false;
            }

            @Override
            public boolean remove(Object o) {
                return s.remove(o);
            }

            @Override
            public boolean containsAll(Collection<?> c) {
                return s.containsAll(c);
            }

            @Override
            public boolean addAll(Collection<? extends E> c) {
                boolean changed = false;
                for (E e : c) {
                    if (!isPresent(e)) {
                        s.add(e);
                        if (!changed)
                            changed = true;
                    }
                }
                return changed;
            }

            @Override
            public boolean retainAll(Collection<?> c) {
                return s.retainAll(c);
            }

            @Override
            public boolean removeAll(Collection<?> c) {
                return s.removeAll(c);
            }

            @Override
            public void clear() {
                s.clear();
            }

            private boolean isPresent(E e) {
                for (int i = 0; i < s.size(); i++) {
                    if (s.comparator != null) {
                        if (s.comparator.compare(s.elementData[i], e) == 0)
                            return false;
                    } else if (s.elementData[i] == e) {
                        return false;
                    }
                }
                return true;
            }

            @Override
            public String toString() {
                return s.toString();
            }
        };
        return set;
    }

    /**
     * Removes all elements from this list. This list will
     * be empty and unsorted after the call returns.
     */
    @Override
    public void clear() {
        for (int i = size; i < capacity; i++) {
            elementData[i] = null;
        }
        size = 0;
        isSorted = false;
        modCount++;
    }

    /**
     * Returns a shallow copy of this {@code DynArray} instance. (The
     * elements themselves are not copied.)
     *
     * @return a clone of this {@code DynArray} instance
     */
    @Override
    @SuppressWarnings("unchecked")
    public Object clone() {
        try {
            DynArray<E> v = (DynArray<E>) super.clone();
            v.elementData = Arrays.copyOf(elementData, size);
            v.modCount = 0;
            return v;
        } catch (CloneNotSupportedException ex) {
            ex.printStackTrace();
            return null; // This should not EVER happen
        }
    }

    /**
     * Trims the capacity of this {@code DynArray} instance to be the
     * list's current size. An application can use this operation to minimize
     * the storage of an {@code DynArray} instance.
     */
    @SuppressWarnings("unchecked")
    public void trimToSize() {
        Object[] shrunk = new Object[size];
        for (int i = 0; i < size; i++) {
            shrunk[i] = elementData[i];
        }
        capacity = size;
        elementData = (E[]) shrunk;
    }

    /**
     * Reverses the order of elements in this {@code DynArray}
     * instance and marks it as <b>unsorted</b>.
     */
    public void reverse() {
        int bound = (size + 1) / 2 - 1;
        for (int i = size - 1; i > bound; i--) {
            E switcheroo = elementData[i];
            elementData[i] = elementData[size - 1 - i];
            elementData[size - 1 - i] = switcheroo;
        }
        isSorted = false;
    }

    /**
     * Returns the index of the first occurrence of the specified element
     * in this list, or -1 if this list does not contain the element.
     * More formally, returns the lowest index {@code i} such that
     * {@code Objects.equals(o, get(i))} or
     * {@code getComparator().compare(o, get(i)) == 0}
     * (if the <i>internal comparator</i> is not {@code null}),
     * or -1 if there is no such index.
     */
    @Override
    public int indexOf(Object o) {
        return indexOf(0, size, o);
    }

    /**
     * Returns the index of the last occurrence of the specified element
     * in this list, or -1 if this list does not contain the element.
     * More formally, returns the lowest index {@code i} such that either
     * {@code Objects.equals(o, get(i))},
     * {@code getComparator().compare(o, get(i)) == 0}
     * (if the <i>internal comparator</i> is not {@code null}),
     * or -1 if there is no such index.
     */
    @Override
    public int lastIndexOf(Object o) {
        return lastIndexOf(0, size, o);
    }

    private int lastLinearIndexOf(int fromIndex, int toIndex, Object o) {
        if (comparator != null)
            return lastLinearIndexOf(fromIndex, toIndex, o, comparator);
        if (size == 0) {
            return -1;
        }
        for (int i = toIndex - 1; i >= fromIndex; i--) {
            if (elementData[i] == null || o == null) {
                if (elementData[i] == o) {
                    return i;
                }
            } else if (elementData[i].equals(o)) {
                return i;
            }
        }
        return -1;
    }

    @SuppressWarnings("unchecked")
    private int lastLinearIndexOf(int fromIndex, int toIndex, Object o, Comparator<? super E> comparator) {
        if (size == 0) {
            return -1;
        }
        for (int i = toIndex - 1; i >= fromIndex; i--) {
            if (comparator.compare(elementData[i], (E) o) == 0)
                return i;
        }
        return -1;
    }

    /**
     * Returns the index of the last occurrence of the specified element
     * in a range of this list, or -1 if the range does not contain the element.
     * More formally, returns the lowest index {@code i} such that either
     * {@code Objects.equals(o, get(i))},
     * {@code getComparator().compare(o, get(i)) == 0}
     * (if the <i>internal comparator</i> is not {@code null}),
     * or -1 if there is no such index.
     * 
     * @param fromIndex the index of the first element (inclusive) to be
     *                  searched
     * @param toIndex   the index of the last element (exclusive) to be searched
     * @param o         the element to search for
     * @return the index of the last occurrence of the specified element
     *         in a range of this list, or -1 if
     *         the range does not contain the element
     */
    @SuppressWarnings("unchecked")
    public int lastIndexOf(int fromIndex, int toIndex, Object o) {
        if (!isSorted) {
            return lastLinearIndexOf(fromIndex, toIndex, o);
        }
        if (size == 0)
            return -1;
        int j;
        j = binarySearch(fromIndex, toIndex, (E) o);
        if (j < 0)
            return -1;
        while (j < size - 1) {
            if (comparator != null && (comparator.compare(elementData[j + 1], (E) o) != 0)) {
                break;
            } else if (elementData[j + 1] == null || o == null) {
                if (elementData[j + 1] != o) {
                    break;
                }
            } else if (!elementData[j + 1].equals(o)) {
                break;
            }
            j++;
        }
        return j;
    }

    // Returns any index of Object o (used for binary optimization)
    @SuppressWarnings("unchecked")
    private int anyIndexOf(int fromIndex, int toIndex, Object o) {
        if (isSorted) {
            if (size == 0)
                return -1;
            int j;
            j = binarySearch(fromIndex, toIndex, (E) o);
            return (j >= 0) ? j : -1;
        } else {
            return linearIndexOf(fromIndex, toIndex, o);
        }
    }

    private int linearIndexOf(int fromIndex, int toIndex, Object o) {
        if (comparator != null)
            return linearIndexOf(fromIndex, toIndex, o, comparator);
        if (size == 0)
            return -1;
        for (int i = fromIndex; i < toIndex; i++) {
            if (elementData[i] == null || o == null) {
                if (elementData[i] == o)
                    return i;
            } else if (elementData[i].equals(o)) {
                return i;
            }
        }
        return -1;
    }

    @Override
    public int hashCode() {
        int hashCode = 1;
        for (int i = 0; i < size; i++) {
            hashCode = 31 * hashCode +
                    (elementData[i] == null ? 0 : elementData[i].hashCode());
        }
        return hashCode;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (obj.hashCode() == this.hashCode())
            return true;
        return false;
    }

    @SuppressWarnings("unchecked")
    private int linearIndexOf(int fromIndex, int toIndex, Object o, Comparator<? super E> c) {
        if (size == 0)
            return -1;
        checkComparator(c);
        for (int i = fromIndex; i < toIndex; i++) {
            if (c.compare(elementData[i], (E) o) == 0)
                return i;
        }
        return -1;
    }

    /**
     * Returns the index of the first occurrence of the specified element
     * in a range of this list, or -1 if the range does not contain the element.
     * More formally, returns the lowest index {@code i} such that either
     * {@code Objects.equals(o, get(i))},
     * {@code getComparator().compare(o, get(i)) == 0}
     * (if the <i>internal comparator</i> is not {@code null}),
     * or -1 if there is no such index.
     * 
     * @param fromIndex the index of the first element (inclusive) to be
     *                  searched
     * @param toIndex   the index of the last element (exclusive) to be searched
     * @param o         the element to search for
     * @return the index of the first occurrence of the specified element
     *         in a range of this list, or -1 if
     *         the range does not contain the element
     */
    @SuppressWarnings("unchecked")
    public int indexOf(int fromIndex, int toIndex, Object o) {
        if (!isSorted) {
            return linearIndexOf(fromIndex, toIndex, o);
        }
        if (size == 0)
            return -1;
        int j = binarySearch(fromIndex, toIndex, (E) o);
        if (j < 0)
            return -1;
        while (j > 0) {
            if (comparator != null && (comparator.compare(elementData[j - 1], (E) o) != 0)) {
                break;
            } else if (elementData[j - 1] == null || o == null) { // do not change this
                if (elementData[j - 1] != o) {
                    break;
                }
            } else if (!elementData[j - 1].equals(o)) {
                break;
            }
            j--;
        }
        return j;
    }

    @Override
    public void replaceAll(UnaryOperator<E> operator) {
        replaceAllRange(operator, 0, size);
    }

    private void replaceAllRange(UnaryOperator<E> operator, int i, int end) {
        Objects.requireNonNull(operator);
        final int expectedModCount = modCount;
        final Object[] es = elementData;
        for (; modCount == expectedModCount && i < end; i++)
            es[i] = operator.apply(elementData[i]);
        if (modCount != expectedModCount)
            throw new ConcurrentModificationException();
    }

    // Exists only to allow the Sublist to function properly
    // doesn't unsort
    protected void resize0(int n) {
        if (n < size) {
            for (int i = n; i < size; i++) {
                elementData[i] = null;
                modCount++;
            }
        } else if (n > size) {
            if (n > capacity)
                ensureCapacity(n);
            modCount++;
        } else if (size == n) {
            return;
        }
        size = n;
    }

    /**
     * Resizes this list to size {@code n}. If {@code n}
     * is larger than {@code size()},
     * this list will be marked as <b>unsorted</b>, since
     * {@code null} elements will be added to the end
     * until {@code size() == n}. Additionally, if {@code n}
     * is larger than {@code getCapacity()}, the capacity of
     * this {@code DynArray} instance will increase by the
     * {@link #setCapacityIncrement(double, boolean) capacity increment}.
     * 
     * @param n the new size of this list
     * @throws IllegalArgumentException if {@code n} is less than 0
     */
    public void resize(int n) {
        if (n < 0)
            throw new IllegalArgumentException();
        isSorted = false;
        resize0(size);
    }

    /**
     * Increases the capacity of this {@code DynArray} instance, if
     * necessary, to ensure that it can hold at least the number of elements
     * specified by the minimum capacity argument.
     *
     * @param minCapacity the desired minimum capacity
     */
    @SuppressWarnings("unchecked")
    public void ensureCapacity(int minCapacity) {
        if (minCapacity > capacity) {
            if (!growsAdditively) {
                if (capacity == 0)
                    capacity = LAZY_INIT_CAPACITY;
                while (capacity < minCapacity) {
                    capacity *= capacityIncrement;
                }
            } else {
                capacity += capacityIncrement;
                if (capacity < minCapacity)
                    capacity = minCapacity;
            }
            Object partial[] = new Object[capacity];
            for (int i = 0; i < size; i++) {
                partial[i] = elementData[i];
            }
            elementData = (E[]) partial;
        }
    }

    /**
     * <p>
     * Sets the increment and mode by which the capacity
     * of this {@code DynArray} instance increases upon
     * {@link #ensureCapacity(int) ensuring a larger capacity},
     * {@link #resize(int) resizing} this {@code DynArray} to a size
     * greater than its capacity, or
     * adding elements such that the resulting size
     * of this {@code DynArray} would be greater than its capacity.
     * </p>
     * 
     * <p>
     * If {@code growAdditively} is
     * {@code false}, {@code DynArray} capacity will be set to increase to the
     * product of itself and {@code increment} (multiplicative incrementation).
     * If {@code growAdditively} is {@code true}, {@code DynArray} capacity will be
     * set to increase to the
     * sum of {@code increment} and itself (additive incrementation).
     * </p>
     * 
     * <p>
     * When a specific {@code DynArray} capacity or size is desired,
     * which is greater than the capacity that would be
     * be attained with a single incrementation,
     * {@code DynArray} capacity will either be multiplied repeatedly by the
     * {@code increment}
     * until that desired capacity is reached (if {@code growAdditively} is
     * {@code false}), or
     * it will be set to equal the desired capacity (if {@code growAdditively} is
     * {@code true}).
     * Such methods in which this could occur include: {@link #ensureCapacity(int)},
     * {@link #resize(int)} and bulk operations such as {@link #addAll(Collection)}.
     * </p>
     * 
     * This method will simply return {@code false} if
     * the specified {@code increment} is not large enough
     * to accomodate for at least one more element after
     * capacity incrementation. ({@code (double) (capacity + 1)/capacity}
     * gives the minimum multiplicative {@code increment} to do so).
     * 
     * @param increment      the increment by which {@code DynArray} capacity
     *                       increases (if needed) upon adding elements,
     *                       {@link #resize(int) resizing}
     *                       or {@link #ensureCapacity(int) ensuring capacity}
     * @param growAdditively if {@code true} the capacity of this {@code DynArray}
     *                       will increase by adding {@code increment}.
     *                       Otherwise, the capacity increase by
     *                       multiplying itself by {@code increment}.
     * 
     * @return {@code true} if either the capacity increment
     *         or mode of incrementation changed as a result of this call
     * @throws IllegalArgumentException if {@code increment} is less than one
     */
    public boolean setCapacityIncrement(double increment, boolean growAdditively) {
        capacityIncrementCheck(increment);
        if ((capacity * increment) / (capacity + 1) < 1.0
                || (increment == this.capacityIncrement
                        && this.growsAdditively == growAdditively)) {
            return false;
        }
        growsAdditively = growAdditively;
        capacityIncrement = increment;
        return true;
    }

    /**
     * Returns the increment by which the capacity of this {@code DynArray}
     * instance expands by, upon running out of space in its backing array.
     * 
     * @return the increment by which this {@code DynArray} instance expands by,
     *         upon running out of space in its backing array
     */
    public double getCapacityIncrement() {
        return capacityIncrement;
    }

    /**
     * Returns {@code true} if the capacity of this {@code DynArray} instance
     * is set to {@link #setCapacityIncrement(double, boolean) increment}
     * additively instead of multiplicatively.
     * 
     * @return true if the capacity of this {@code DynArray}
     *         instance is set to increment additively
     */
    public boolean growsAdditively() {
        return growsAdditively;
    }

    /**
     * Returns the indices at which the specified element is present this list.
     * If {@code o} is not present, an array of length zero is returned.
     * 
     * @param o the element to search for
     * @return the indices at which the specified element is present this list
     */
    public int[] indicesOf(Object o) {
        return indicesOf(0, size, o);
    }

    /**
     * Returns the indices at which the specified element is present
     * in a range of this {@code DynArray} instance.
     * If {@code o} is not present in the range, an array of length zero is
     * returned.
     *
     * @param fromIndex the index of the first element (inclusive) to be
     *                  searched
     * @param toIndex   the index of the last element (exclusive) to be searched
     * @param o         the element to search for
     * @return the indices at which the specified element is present in the range
     */
    public int[] indicesOf(int fromIndex, int toIndex, Object o) {
        rangeCheck(fromIndex, toIndex);
        int count = 0;
        int husk[] = new int[toIndex - fromIndex];
        for (int index = indexOf(fromIndex, toIndex, o); index != -1; index = linearIndexOf(index + 1, toIndex, o)) {
            if (index > -1) {
                count++;
                husk[count - 1] = index;
            }
        }
        int[] result = new int[count];
        for (int i = 0; i < count; i++) {
            result[i] = husk[i];
        }
        return result;
    }

    // Removes an index and shifts everything along
    // Increases modCount
    private void eraseAndMod(int index) {
        int expectedModCount = modCount;
        elementData[index] = null;
        for (int i = index; i < size - 1; i++) {
            elementData[i] = elementData[i + 1];
        }
        elementData[size - 1] = null;
        size--;
        modCount++;
        checkForComodification(expectedModCount);
    }

    // Removes an index and shifts everything along
    // Does not increase modCount
    private void erase(int index) {
        int expectedModCount = modCount;
        elementData[index] = null;
        for (int i = index; i < size - 1; i++) {
            elementData[i] = elementData[i + 1];
        }
        elementData[size - 1] = null;
        size--;
        checkForComodification(expectedModCount);
    }

    /**
     * Removes the elements in the specified range of this list.
     * Shifts any subsequent elements to the left (subtracts one
     * from their indices). Returns the elements that were removed from the
     * list, or {@code null} if {@code fromIndex == toIndex}.
     *
     * @param fromIndex the index of the first element (inclusive)
     *                  to be removed
     * @param toIndex   the index of the last element (exclusive)
     *                  to be removed
     * @return the elements previously in the range
     * @throws IndexOutOfBoundsException if the index is out of range
     *                                   ({@code index < 0 || index >= size()})
     */
    @SuppressWarnings("unchecked")
    public E[] remove(int fromIndex, int toIndex) {
        rangeCheck(fromIndex, toIndex);
        final int range = toIndex - fromIndex;
        if (range == 0)
            return null;
        Object[] partial = new Object[range];
        for (int i = fromIndex; i < toIndex; i++) {
            partial[i - fromIndex] = elementData[i];
            elementData[i] = null;
        }
        // Multi-erase:
        for (int i = fromIndex; i < size - range; i++) {
            elementData[i] = elementData[i + range];
        }
        for (int j = 0; j < range; j++) {
            elementData[size - j - 1] = null;
        }
        size -= range;
        modCount++;
        return (E[]) partial;
    }

    /**
     * <p>
     * Inserts all of the elements in the specified collection into this
     * list, starting at the specified position. Shifts the element
     * currently at that position (if any) and any subsequent elements to
     * the right (increases their indices). The new elements will appear
     * in the list in the order that they are returned by the
     * specified collection's iterator.
     * </p>
     * 
     * If this list changed as a result
     * of the call, it is also marked as <b>unsorted</b>.
     *
     * @param index index at which to insert the first element from the
     *              specified collection
     * @param c     collection containing elements to be added to this list
     * @return {@code true} if this list changed as a result of the call
     * @throws IndexOutOfBoundsException {@inheritDoc}
     */
    @Override
    public boolean addAll(int index, Collection<? extends E> c) {
        if (c != this) {
            addIndexCheck(index);
            int count = 0;
            int colsize = c.size();
            resize0(size + colsize);
            for (int i = size - 1; i > colsize + index - 1; i--) {
                elementData[i] = elementData[i - colsize];
            }
            for (E e : c) {
                elementData[index + count] = e;
                count++;
            }
            if (batchSorting) {
                sort();
            } else {
                isSorted = checkSorting(index, index + c.size() + 1);
            }
            return true;
        } else {
            @SuppressWarnings("unchecked")
            E[] elDa = (E[]) new Object[size];
            for (int i = 0; i < size; i++) {
                elDa[i] = elementData[i];
            }
            return addAll(index, elDa);
        }
    }

    /**
     * Replaces the element at the specified position
     * in this list with the specified element. If this
     * list becomes unsorted as a result of the call, the
     * {@code DynArray} will be marked as <b>unsorted</b>.
     */
    @Override
    public E set(int index, E element) {
        E oldElement = elementData[index];
        elementData[index] = element;
        isSorted = checkSorting(index, index + 2);
        return oldElement;
    }

    /**
     * Trades elements of this {@code DynArray} instance with
     * elements of {@code externalData} in ascending
     * index order (starting at {@code atIndex} in this list and
     * index 0 in {@code externalData}).
     * 
     * Trading continues until either this list runs out
     * of space at its current size or there are no more elements
     * in {@code externalData} to trade with.
     * 
     * This list is marked as <b>unsorted</b> as a
     * result of the call.
     * 
     * For example, given a {@code DynArray} instance {@code vect}
     * of 3 elements [a, b, c] and an array {@code letters}
     * with elements [x, y],
     * calling {@code vect.tradeData(1, letters)}
     * will result in {@code vect} containing elements
     * [a, x, y] and {@code letters} containing
     * {b, c}.
     * 
     * @param atIndex      the first index of this {@code DynArray} instance
     *                     to trade elements from
     * @param externalData the array of external elements to trade with
     * @param <T>          the type (or subtype) of this list's elements
     * 
     */
    public <T extends E> void tradeData(int atIndex, T[] externalData) {
        tradeData(atIndex, size, externalData, 0);
    }

    /**
     * Trades elements of this {@code DynArray} instance with
     * elements of {@code externalData} in ascending
     * index order (starting at {@code atIndex} (inclusive) and ending at
     * {@code untilIndex} (exclusive) in this list and index 0 in
     * {@code externalData}).
     * 
     * Trading continues until either this list runs out
     * of space at its current size or there are no more elements
     * in {@code externalData} to trade with.
     * 
     * This list is marked as <b>unsorted</b> as a
     * result of the call.
     * 
     * For example, given a {@code DynArray} instance {@code vect}
     * of 3 elements [a, b, c] and an array {@code letters}
     * with elements [x, y],
     * calling {@code vect.tradeData(1, letters)}
     * will result in {@code vect} containing elements
     * [a, x, y] and {@code letters} containing
     * {b, c}.
     * 
     * @param atIndex      the first index of this {@code DynArray} instance
     *                     to trade elements from
     * @param untilIndex   the last possible index of this {@code DynArray} instance
     *                     to
     *                     trade elements from
     * @param externalData the array to trade elements with
     * @param fromExtIndex the starting index in {@code externalData} to trade
     *                     elements
     *                     with
     */
    @SuppressWarnings("unchecked")
    public <T extends E> void tradeData(int atIndex, int untilIndex, T[] externalData, int fromExtIndex) {
        rangeCheck(atIndex, untilIndex);
        if (fromExtIndex > externalData.length - 1 || fromExtIndex < 0) {
            throw new ArrayIndexOutOfBoundsException(
                    "Index " + fromExtIndex + " out of bounds for length " + externalData.length);
        }
        for (int intIndex = atIndex, j = 0; intIndex < untilIndex; intIndex++, j++) {
            if (j < externalData.length - fromExtIndex) {
                E switcheroo = elementData[intIndex];
                elementData[intIndex] = externalData[fromExtIndex + j];
                externalData[fromExtIndex + j] = (T) switcheroo;
            } else {
                break;
            }
        }
        isSorted = false;
    }

    /**
     * {@inheritDoc}
     * 
     * @throws IndexOutOfBoundsException {@inheritDoc}
     */
    @Override
    public E remove(int index) {
        indexCheck(index);
        E oldElement = elementData[index];
        eraseAndMod(index);
        return oldElement;
    }

    /**
     * {@inheritDoc}
     * 
     * @throws NullPointerException if the specified filter is null
     */
    @Override
    public boolean removeIf(Predicate<? super E> filter) {
        return removeIf(filter, 0, size);
    }

    /**
     * Removes all of the elements in the specified range of this collection
     * that satisfy the given predicate.
     * Errors or runtime exceptions thrown during iteration or by
     * the predicate are relayed to the caller.
     *
     * @param filter    a predicate which returns {@code true} for elements to be
     *                  removed
     * @param fromIndex the index of the first element (inclusive)
     *                  to be evaluated by the predicate
     * @param toIndex   the index of the last element (exclusive)
     *                  to be evaluated by the predicate
     * @return {@code true} if any elements were removed
     * @throws NullPointerException if the specified filter is null
     */
    public boolean removeIf(Predicate<? super E> filter, int fromIndex, int toIndex) {
        Objects.requireNonNull(filter);
        int expectedModCount = modCount;
        int pureEnd = toIndex;
        boolean changed = false;
        for (int i = fromIndex; i < pureEnd; i++) {
            if (i > pureEnd)
                throw new ConcurrentModificationException();
            if (filter.test(elementData[i])) {
                if (i == fromIndex)
                    checkForComodification(expectedModCount);
                erase(i);
                changed = true;
                i--;
                pureEnd--;
            }
        }
        checkForComodification(expectedModCount);
        return changed;
    }

    /**
     * Removes consecutive elements of this collection,
     * starting from index 0, until an element in this collection
     * does not satisfy the given predicate.
     * Errors or runtime exceptions thrown during iteration or by
     * the predicate are relayed to the caller.
     *
     * @param filter a predicate which returns {@code true} for elements to be
     *               removed
     * @return {@code true} if any elements were removed
     * @throws NullPointerException if the specified filter is null
     */
    public boolean removeWhile(Predicate<? super E> filter) {
        return removeWhile(filter, 0, size);
    }

    /**
     * Removes consecutive elements in the specified range of this collection,
     * starting at {@code fromIndex}, until an element in range
     * does not satisfy the given predicate.
     * Errors or runtime exceptions thrown during iteration or by
     * the predicate are relayed to the caller.
     *
     * @param filter    a predicate which returns {@code true} for elements to be
     *                  removed
     * @param fromIndex the index of the first element (inclusive)
     *                  to be evaluated by the predicate
     * @param toIndex   the index of the last element (exclusive)
     *                  to be evaluated by the predicate
     * @return {@code true} if any elements were removed
     * @throws NullPointerException if the specified filter is null
     */
    public boolean removeWhile(Predicate<? super E> filter, int fromIndex, int toIndex) {
        Objects.requireNonNull(filter);
        rangeCheck(fromIndex, toIndex);
        int expectedModCount = modCount;
        int pureEnd = size;
        int passage = 0;
        boolean changed = false;
        while (filter.test(elementData[fromIndex])
                && fromIndex < pureEnd
                && passage < toIndex - fromIndex) {
            if (passage == 0)
                checkForComodification(expectedModCount);
            if (fromIndex >= pureEnd)
                throw new ConcurrentModificationException();
            erase(fromIndex);
            changed = true;
            passage++;
        }
        return changed;
    }

    @Override
    public ListIterator<E> listIterator() {
        return new Litr(0);
    }

    @Override
    public ListIterator<E> listIterator(int index) {
        indexCheck(index);
        return new Litr(index);
    }

    class Litr extends Itr implements ListIterator<E> {
        public Litr(int index) {
            this.i = index - 1;
        }

        @Override
        public boolean hasNext() {
            return i < size - 1;
        }

        @Override
        public boolean hasPrevious() {
            return i > -1;
        }

        @Override
        public E previous() {
            if (i <= 0)
                throw new NoSuchElementException();
            if (i >= elementData.length)
                throw new ConcurrentModificationException();
            i--;
            checkForComodification();
            return elementData[i];
        }

        @Override
        public int nextIndex() {
            return i + 1;
        }

        @Override
        public int previousIndex() {
            return i - 1;
        }

        @Override
        public void set(E e) {
            if (lastRet == -1) {
                throw new IllegalArgumentException();
            }
            try {
                DynArray.this.set(i, e);
            } catch (IndexOutOfBoundsException ex) {
                throw new ConcurrentModificationException();
            }
            checkForComodification();
        }

        @Override
        public void add(E e) {
            if (lastRet == -1) {
                throw new IllegalArgumentException();
            }
            try {
                DynArray.this.add(i, e);
                expectedModCount++;
            } catch (IndexOutOfBoundsException ex) {
                throw new ConcurrentModificationException();
            }
            checkForComodification();
        }
    }

    /**
     * Creates a <em><a href="Spliterator.html#binding">late-binding</a></em>
     * and <em>fail-fast</em> {@link Spliterator} over the elements in this
     * list.
     *
     * <p>
     * The {@code Spliterator} reports {@link Spliterator#SIZED},
     * {@link Spliterator#SUBSIZED}, and {@link Spliterator#ORDERED}.
     * If the DynArray has been marked as <i>sorted</i> it will also report
     * {@link Spliterator#SORTED}.
     * </p>
     *
     * Calculating {@code size() / 2} will give the number of times
     * {@link #trySplit()} may be called on an unsplit {@code Spliterator}
     * over the whole {@code DynArray} without returning {@code null}.
     * 
     * @return a {@code Spliterator} over the elements in this list
     */
    @Override
    public Spliterator<E> spliterator() {
        return new Splitr(0, size);
    }

    /**
     * Creates a <em><a href="Spliterator.html#binding">late-binding</a></em>
     * and <em>fail-fast</em> {@link Spliterator} over the elements in this
     * list.
     *
     * <p>
     * The {@code Spliterator} reports {@link Spliterator#SIZED},
     * {@link Spliterator#SUBSIZED}, and {@link Spliterator#ORDERED}.
     * If the DynArray has been marked as <b>sorted</b> it will also report
     * {@link Spliterator#SORTED}.
     * </p>
     *
     * <p>
     * Calculating {@code size() / 2} will give the number of times
     * {@link #trySplit()} may be called on an unsplit {@code Spliterator}
     * over the whole {@code DynArray} without returning {@code null},
     * unsplit meaning a spliterator generated with <i>this</i> method call.
     * and not {@code trySplit()}.
     * </p>
     *
     * When {@code trySplit()} is called on a {@code DynArray} spliterator,
     * instead of the muddled {@code ArrayList} one, the order of elements
     * is preserved such that if the newly created spliterator returned
     * from {@code trySplit()} was appended to the calling spliterator,
     * elements would be in list index order. e.g. [2,3,4] trySplit -> [2] (old)
     * and [3,4] (new). The "new" spliterator will always contain more elements
     * than the spliterator it was generated from (at its time of creation).
     *
     * @return a {@code Spliterator} over the elements in this list
     */
    public Spliterator<E> spliterator(int fromIndex, int toIndex) {
        return new Splitr(fromIndex, toIndex);
    }

    class Splitr implements Spliterator<E> {
        int i = -1;
        int peak, fence, origin;
        int expectedModCount = modCount;

        public Splitr(int fromIndex, final int toIndex) {
            origin = fromIndex;
            this.peak = toIndex;
            this.fence = toIndex;
        }

        @Override
        public boolean tryAdvance(Consumer<? super E> action) {
            if (action == null)
                throw new NullPointerException();
            checkForComodification();
            if (fence < peak)
                fence++;
            if (i < peak) {
                action.accept(elementData[i]);
                i++;
                checkForComodificationNoBind();
                return true;
            } else {
                return false;
            }
        }

        @Override
        public void forEachRemaining(Consumer<? super E> action) {
            if (action == null)
                throw new NullPointerException();
            checkForComodification();
            int j = i;
            if (fence < peak)
                fence++;
            while (i < peak) {
                fence++;
                action.accept(get(i));
                if (i == j)
                    checkForComodification(); // avoiding repeated checks
                i++;
            }
        }

        /**
         * <p>
         * When {@code trySplit()} is called on a {@code DynArray} spliterator,
         * instead of the muddled {@code ArrayList} one, the order of elements
         * is preserved such that if the newly created spliterator returned
         * from {@code trySplit()} was appended to the calling spliterator,
         * elements would be in list index order. e.g. [2,3,4] trySplit -> [2] (old)
         * and [3,4] (new). The "new" spliterator will always contain more elements
         * than the spliterator it was generated from (at its time of creation).
         * </p>
         * {@inheritDoc}}
         */
        @Override
        public Spliterator<E> trySplit() {
            checkForComodification();
            Splitr split = null;
            if (i < peak) {
                checkForComodificationNoBind();
                fence = origin + ((peak - origin + 1) >>> 1) - 1; // better not to question it...
                split = new Splitr(fence, peak);
                peak = fence;
            }
            return split;
        }

        @Override
        public long estimateSize() {
            checkForComodification();
            return fence - i;
        }

        @Override
        public int characteristics() {
            return (isSorted) ? Spliterator.SORTED | Spliterator.ORDERED |
                    Spliterator.SIZED | Spliterator.SUBSIZED
                    : Spliterator.ORDERED | Spliterator.SIZED | Spliterator.SUBSIZED;
        }

        @Override
        public Comparator<? super E> getComparator() {
            if (!isSorted)
                throw new IllegalStateException("DynArray is not marked as <b>sorted</b>");
            return comparator;
        }

        protected void checkForComodification() {
            if (i == -1)
                i = origin; // late-binding
            if (modCount != expectedModCount)
                throw new ConcurrentModificationException(); // fail-fast
        }

        protected void checkForComodificationNoBind() {
            if (modCount != expectedModCount)
                throw new ConcurrentModificationException();
        }
    }

    /**
     * {@inheritDoc}
     * <p>
     * <b> Note: there are very few reasons to call this
     * method on a {@code DynArray}
     * due to the abundance of range-based methods. </b>
     * </p>
     * 
     */
    @Override
    public List<E> subList(int fromIndex, int toIndex) {
        rangeCheck(fromIndex, toIndex);
        return new SubDynArray<E>(fromIndex, toIndex, this);
    }

    static final class SubDynArray<E> extends DynArray<E> {
        final int offset;
        DynArray<E> parent;

        @SuppressWarnings("unchecked")
        public SubDynArray(int fromIndex, int toIndex, DynArray<E> parent) {
            this.parent = parent;
            this.modCount = parent.modCount;
            this.offset = fromIndex;
            this.size = toIndex - fromIndex;
            this.capacity = size;
            this.elementData = (E[]) new Object[capacity];
            this.batchSorting = parent.batchSorting;
            this.isSorted = parent.isSorted;
            this.comparator = parent.comparator;
            for (int i = 0; i < size; i++) {
                elementData[i] = parent.elementData[offset + i];
            }
        }

        @Override
        public boolean add(E e) {
            parent.add(endInParent(), e);
            super.add(e);
            checkForParentModification();
            return true;
        }

        @Override
        public void add(int index, E e) {
            super.add(index, e);
            parent.add(offset + index, e);
            checkForParentModification();
        }

        @Override
        public boolean addAll(Collection<? extends E> c) {
            parent.addAll(endInParent(), c);
            boolean ret = super.addAll(c);
            checkForParentModification();
            return ret;
        }

        @Override
        public boolean addAll(E[] a) {
            parent.addAll(endInParent(), a);
            boolean ret = super.addAll(a);
            checkForParentModification();
            return ret;
        }

        @Override
        public boolean addAll(int index, Collection<? extends E> c) {
            parent.addAll(offset + index, c);
            boolean ret = super.addAll(index, c);
            checkForParentModification();
            return ret;
        }

        @Override
        public boolean addAll(int index, E[] a) {
            parent.addAll(offset + index, a);
            boolean ret = super.addAll(index, a);
            checkForParentModification();
            return ret;
        }

        @Override
        public void clear() {
            if (size != 0) {
                parent.remove(offset, endInParent());
            } else {
                modCount--; // Avoiding a false-positive CME
            }
            super.clear();
            checkForParentModification();
        }

        @Override
        public void forEach(Consumer<? super E> action) {
            checkForParentModification();
            super.forEach(action);
        }

        @Override
        public Iterator<E> iterator() {
            return new SubItr();
        }

        class SubItr extends Itr {
            @Override
            public void remove() {
                checkForComodification();
                if (lastRet == -1)
                    throw new IllegalStateException();
                try {
                    SubDynArray.this.remove(lastRet);
                    parent.remove(lastRet + offset);
                    expectedModCount++;
                    i--;
                } catch (IndexOutOfBoundsException ex) {
                    throw new ConcurrentModificationException();
                }
            }

            @Override
            protected void checkForComodification() {
                if (modCount != expectedModCount)
                    throw new ConcurrentModificationException();
                checkForParentModification();
            }
        }

        @Override
        public ListIterator<E> listIterator() {
            return new SubLitr(0);
        }

        @Override
        public ListIterator<E> listIterator(int fromIndex) {
            super.indexCheck(fromIndex);
            return new SubLitr(fromIndex);
        }

        class SubLitr extends SubItr implements ListIterator<E> {
            public SubLitr(int index) {
                this.i = index - 1;
            }

            public boolean hasNext() {
                return i < size - 1;
            }

            public boolean hasPrevious() {
                return i > -1;
            }

            @Override
            public E previous() {
                if (i <= 0)
                    throw new NoSuchElementException();
                if (i >= elementData.length)
                    throw new ConcurrentModificationException();
                i--;
                checkForComodification();
                return elementData[i];
            }

            public int nextIndex() {
                return i + 1;
            }

            public int previousIndex() {
                return i - 1;
            }

            @Override
            public void set(E e) {
                if (lastRet == -1) {
                    throw new IllegalArgumentException();
                }
                try {
                    SubDynArray.this.set(i, e);
                    parent.set(offset + i, e);
                } catch (IndexOutOfBoundsException ex) {
                    throw new ConcurrentModificationException();
                }
                checkForComodification();
            }

            @Override
            public void add(E e) {
                if (lastRet == -1) {
                    throw new IllegalArgumentException();
                }
                try {
                    SubDynArray.this.add(i, e);
                    parent.add(offset + i, e);
                    expectedModCount++;
                } catch (IndexOutOfBoundsException ex) {
                    throw new ConcurrentModificationException();
                }
                checkForComodification();
            }
        }

        @Override
        public boolean remove(int fromIndex, int toIndex, Object o) {
            boolean changed = parent.remove(fromIndex + offset, toIndex + offset, o);
            super.remove(fromIndex, toIndex, o);
            checkForParentModification();
            return changed;
        }

        @Override
        public E remove(int index) {
            parent.remove(offset + index);
            E e = super.remove(index);
            checkForParentModification();
            return e;
        }

        @Override
        public E[] remove(int fromIndex, int toIndex) {
            parent.remove(fromIndex + offset, toIndex + offset);
            E[] e = super.remove(fromIndex, toIndex);
            checkForParentModification();
            return e;
        }

        @Override
        public boolean removeAll(Collection<?> c) {
            parent.removeAll(offset, endInParent(), c);
            boolean changed = super.removeAll(0, size, c);
            checkForParentModification();
            return changed;
        }

        @Override
        public boolean removeAll(int fromIndex, int toIndex, Collection<?> c) {
            parent.removeAll(fromIndex + offset, toIndex + offset, c);
            boolean changed = super.removeAll(fromIndex, toIndex, c);
            checkForParentModification();
            return changed;
        }

        @Override
        public boolean removeAll(int fromIndex, int toIndex, Object o) {
            parent.removeAll(fromIndex + offset, toIndex + offset, o);
            boolean changed = super.removeAll(fromIndex, toIndex, o);
            checkForParentModification();
            return changed;
        }

        @Override
        public boolean removeAll(int fromIndex, int toIndex, Object[] a) {
            parent.removeAll(fromIndex + offset, toIndex + offset, a);
            boolean changed = super.removeAll(fromIndex, toIndex, a);
            checkForParentModification();
            return changed;
        }

        @Override
        public boolean removeIf(Predicate<? super E> filter, int fromIndex, final int toIndex) {
            parent.removeIf(filter, fromIndex + offset, toIndex + offset);
            boolean changed = super.removeIf(filter, fromIndex, toIndex);
            checkForParentModification();
            return changed;
        }

        @Override
        public boolean removeNulls() {
            int[] result = parent.indicesOf(offset, endInParent(), null);
            for (int i = 0; i < result.length; i++) {
                parent.erase(result[i] - i);
                super.erase(result[i - offset] - i);
            }
            checkForParentModification();
            if (result.length > 0) {
                parent.modCount++;
                this.modCount++;
                return true;
            } else {
                return false;
            }
        }

        @Override
        public boolean removeWhile(Predicate<? super E> filter, int fromIndex, int toIndex) {
            parent.removeWhile(filter, fromIndex + offset, toIndex + offset);
            boolean changed = super.removeWhile(filter, fromIndex, toIndex);
            checkForParentModification();
            return changed;
        }

        @Override
        public void resize(int n) {
            checkForParentModification();
            if (n < size) {
                for (int i = n; i < size; i++) {
                    elementData[i] = null;
                    parent.eraseAndMod(i + offset);
                    modCount++;
                }
            } else if (n > size) {
                if (n > capacity)
                    ensureCapacity(n);
                nullPaddingToParent(n - size);
                if (n < parent.size)
                    parent.modCount++; // Prevents CME
                modCount++;
                isSorted = false;
            } else if (size == n) {
                return;
            }
            size = n;
        }

        @Override
        protected void resize0(int n) {
            if (n < size) {
                for (int i = n; i < size; i++) {
                    elementData[i] = null;
                    parent.erase(i + offset); // Not @eraseAndMod because resize0 is only called internally
                }
            } else if (n > size) {
                if (n > capacity)
                    ensureCapacity(n);
                modCount++;
            } else if (size == n) {
                return;
            }
            size = n;
        }

        @Override
        public boolean retainAll(int fromIndex, int toIndex, Object o) {
            parent.retainAll(fromIndex + offset, toIndex + offset, o);
            boolean changed = super.retainAll(0, size, o);
            checkForParentModification();
            return changed;
        }

        @Override
        public boolean retainAll(int fromIndex, int toIndex, Collection<?> c) {
            parent.retainAll(fromIndex + offset, toIndex + offset, c);
            boolean changed = super.retainAll(0, size, c);
            checkForParentModification();
            return changed;
        }

        @Override
        public boolean retainAll(int fromIndex, int toIndex, Object[] a) {
            parent.retainAll(fromIndex + offset, toIndex + offset, a);
            boolean changed = super.retainAll(0, size, a);
            checkForParentModification();
            return changed;
        }

        @Override
        public void reverse() {
            if (size <= 1)
                return;
            int bound = (size + 1) / 2 - 1;
            for (int i = size - 1; i > bound; i--) {
                E switcheroo = elementData[i];
                elementData[i] = elementData[size - 1 - i];
                elementData[size - 1 - i] = switcheroo;
            }
            correctMain();
            isSorted = false;
            checkForParentModification();
        }

        @Override
        public E set(int index, E element) {
            E ret = super.set(index, element); // No parent method call for optimization
            parent.elementData[index + offset] = element;
            parent.isSorted = false;
            checkForParentModification();
            return ret;
        }

        @Override
        public void shuffle() {
            super.shuffle();
            correctMain();
        }

        @Override
        public boolean sift() {
            int preSize = size;
            if (super.sift()) {
                for (int i = 0; i < preSize - size; i++) {
                    parent.erase(endInParent() - 1);
                }
                correctMain();
                parent.modCount++;
                return true;
            } else {
                return false;
            }
        }

        @Override
        public void sort() {
            super.sort();
            correctMain();
        }

        @Override
        public void sort(Comparator<? super E> c) {
            super.sort(c);
            correctMain();
        }

        @Override
        public Spliterator<E> spliterator() {
            return new SubSplitr(0, size);
        }

        @Override
        public Spliterator<E> spliterator(int fromIndex, int toIndex) {
            return new SubSplitr(fromIndex, toIndex);
        }

        class SubSplitr extends Splitr {
            public SubSplitr(int fromIndex, int toIndex) {
                super(fromIndex, toIndex);
            }

            @Override
            public int characteristics() {
                return super.characteristics();
            }

            @Override
            public long estimateSize() {
                checkForParentModification();
                return super.estimateSize();
            }

            @Override
            public void forEachRemaining(Consumer<? super E> action) {
                checkForParentModification();
                super.forEachRemaining(action);
            }

            @Override
            public boolean tryAdvance(Consumer<? super E> action) {
                checkForParentModification();
                return super.tryAdvance(action);
            }

            @Override
            public Spliterator<E> trySplit() {
                checkForParentModification();
                return super.trySplit();
            }
        }

        @Override
        public void swap(int i, int j) {
            super.swap(i, j);
            parent.elementData[i + offset] = elementData[j];
            parent.elementData[j + offset] = elementData[i];
            parent.modCount++;
            checkForParentModification();
        }

        @Override
        public <T extends E> void tradeData(int atIndex, int untilIndex,
                T[] externalData, int fromExtIndex) {
            super.tradeData(atIndex, untilIndex, externalData, fromExtIndex);
            correctMain(atIndex, untilIndex);
        }

        private void nullPaddingToParent(int count) {
            for (int i = 0; i < count; i++) {
                parent.add(endInParent() + i, null);
                parent.modCount--;
            }
        }

        protected int endInParent() {
            return offset + size;
        }

        private void checkForParentModification() {
            if (parent.modCount != modCount) {
                throw new ConcurrentModificationException(
                        "DynArray modified prior to subList method call");
            }
        }

        // For methods that guarantee a modCount increase
        private void correctMain() {
            correctMain(0, size);
        }

        private void correctMain(int fromSubIndex, int toSubIndex) {
            for (int i = fromSubIndex; i < toSubIndex; i++) {
                parent.elementData[i + offset] = elementData[i];
            }
        }
    }

    // fromIndex must be leq toIndex and gtr 0.
    // toIndex must be leq size.
    private void rangeCheck(int fromIndex, int toIndex) {
        if (fromIndex > toIndex) {
            throw new IllegalArgumentException(
                    "fromIndex(" + fromIndex + ") > toIndex(" + toIndex + ")");
        }
        if (fromIndex < 0) {
            throw new IndexOutOfBoundsException(
                    "index " + fromIndex + " out of range for DynArray size " + size);
        }
        if (toIndex > size) {
            throw new IndexOutOfBoundsException(
                    "index " + toIndex + " out of range for DynArray size " + size);
        }
    }

    // acceptable index to add elements is from 0
    // up to (and including) DynArray size
    private void addIndexCheck(int index) {
        if (index > size) {
            throw new IndexOutOfBoundsException(
                    "Index " + index + " is out of bounds for adding to DynArray of size " + size);
        } else if (index < 0) {
            throw new IndexOutOfBoundsException(
                    "Index " + index + " out of bounds for DynArray size " + size);
        }
    }

    private void indexCheck(int index) {
        if (index >= size || index < 0) {
            throw new IndexOutOfBoundsException(
                    "index " + index + " out of bounds for DynArray size " + size + ".");
        }
    }

    // Will set a boolean to true and fast-return if it's already true.
    private boolean checkChange(boolean bool) {
        if (bool) {
            return true;
        } else {
            bool = true;
            modCount++;
            return bool;
        }
    }

    private void capacityCheck(int capacity) {
        if (capacity < 0) {
            throw new IllegalArgumentException(
                    "Illegal Capacity: " + capacity);
        }
    }

    private void capacityIncrementCheck(double increment) {
        if (increment < 1) {
            throw new IllegalArgumentException(
                    "Illegal Capacity Increment: " + capacity);
        }
    }

    private void checkForComodification(int expectedModCount) {
        if (expectedModCount != modCount) {
            throw new ConcurrentModificationException();
        }
    }

    @SuppressWarnings("unchecked")
    private boolean checkSorting(int fromIndex, int toIndex) {
        int range = toIndex - fromIndex;
        if (size == range && !isSorted)
            return false;
        if (size == 1)
            return true;
        if (toIndex > size) { // Rare corner case
            toIndex--;
            fromIndex--;
        }
        Comparator<? super E> comp;
        if (comparator == null) {
            comp = (Comparator<? super E>) Comparator.naturalOrder();
        } else {
            comp = comparator;
        }
        if ((!(elementData[0] instanceof Comparable) && comparator == null))
            return false;
        try {
            for (int i = fromIndex; i < toIndex - 1; i++) {
                if (!(comp.compare(elementData[i + 1], elementData[i]) >= 0)) {
                    return false;
                }
            }
        } catch (NullPointerException e) {
            return false;
        }
        return true;
    }
}