import { act, fireEvent, render, screen } from '@testing-library/react';
import { expect, it, vi } from 'vitest';
import { MotionProvider } from '@/components/exhibit-motion';
import { PathChapter, PathFlow } from '@/components/reader-paths';
import {
  chapterInfo,
  readerPaths,
  type ChapterId,
  type PathId,
} from '@/lib/reader-paths';
import { installMotionPreference } from './setup';

function Flow({ path }: { path: PathId }) {
  return (
    <MotionProvider>
      <PathFlow selected={path} key={path}>
        {(Object.keys(chapterInfo) as ChapterId[]).map((chapter) => (
          <PathChapter chapter={chapter} key={chapter}>
            <section id={chapter}>
              <h2>{chapterInfo[chapter].title}</h2>
              {chapter === 'physics' && (
                <>
                  <a href="#representations">Open refresher</a>
                  <div id="charge-key">Charges</div>
                </>
              )}
              {chapter === 'foundations' && (
                <details>
                  <summary>Technical detail</summary>
                  <div id="representations">Representation</div>
                  <a href="#charge-key">Return to charges</a>
                </details>
              )}
            </section>
          </PathChapter>
        ))}
      </PathFlow>
    </MotionProvider>
  );
}

for (const path of readerPaths)
  it(`mounts the exact ${path.id} chapter order`, async () => {
    const view = render(<Flow path={path.id} />);
    await act(async () => {
      await Promise.resolve();
    });
    expect(
      [...view.container.querySelectorAll('.path-chapter')].map((n) =>
        n.getAttribute('data-chapter'),
      ),
    ).toEqual(path.chapters);
    for (const id of Object.keys(chapterInfo) as ChapterId[]) {
      expect(!!view.container.querySelector('#' + id)).toBe(
        path.chapters.includes(id),
      );
    }
  });

it('mounts an optional chapter, opens its detail, focuses it, and returns without smooth motion', async () => {
  vi.useFakeTimers();
  installMotionPreference(true);
  const scroll = vi.fn();
  Object.defineProperty(HTMLElement.prototype, 'scrollIntoView', {
    configurable: true,
    value: scroll,
  });
  const view = render(<Flow path="physics" />);
  await act(async () => {
    await Promise.resolve();
  });
  expect(view.container.querySelector('#foundations')).toBeNull();
  fireEvent.click(screen.getByRole('link', { name: 'Open refresher' }));
  await act(async () => {
    vi.advanceTimersByTime(20);
  });
  expect(location.hash).toBe('#representations');
  expect(document.activeElement?.id).toBe('representations');
  expect(view.container.querySelector('details')?.open).toBe(true);
  expect(scroll).toHaveBeenLastCalledWith({
    behavior: 'instant',
    block: 'start',
  });
  fireEvent.click(screen.getByRole('link', { name: 'Return to charges' }));
  await act(async () => {
    vi.advanceTimersByTime(20);
  });
  expect(document.activeElement?.id).toBe('charge-key');
  expect(location.hash).toBe('#charge-key');
  view.unmount();
  expect(vi.getTimerCount()).toBe(0);
});

it('opens an omitted chapter on an initial deep link', async () => {
  vi.useFakeTimers();
  history.replaceState(null, '', '/?path=physics#representations');
  Object.defineProperty(HTMLElement.prototype, 'scrollIntoView', {
    configurable: true,
    value: vi.fn(),
  });
  const view = render(<Flow path="physics" />);
  await act(async () => {
    await Promise.resolve();
    vi.advanceTimersByTime(20);
  });
  expect(view.container.querySelector('#foundations')).toBeTruthy();
  expect(document.activeElement?.id).toBe('representations');
});
